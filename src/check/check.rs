use std::{
    collections::{HashMap as Map, HashSet as Set},
    fmt::Display,
    ops::Deref,
    rc::Rc,
};

use ariadne::{Label, Report, ReportKind};

use crate::syntax::ast::{AdtDef, Ast, Clause, FunctionDef, Literal, Span, Spanned};

use super::{
    context::Ctx,
    env::Env,
    expr::{Cons, ConsRef, Expr, FunRef},
    r#type::{Fresh, PrimType, Scheme, Type, TypePrinter, TypeVar},
};

pub trait Types {
    fn ftv(&self) -> Set<TypeVar>;
    fn apply(&mut self, s: &Subst);
}

impl Types for Type {
    fn ftv(&self) -> Set<TypeVar> {
        match self {
            Type::Scheme(s) => s.ftv(),
            Type::Var(v) => [*v].into(),
            Type::Lam(x, y) => x.ftv().union(&y.ftv()).copied().collect(),
            Type::Adt(_) => Set::new(),
            Type::Prim(_) => Set::new(),
        }
    }

    fn apply(&mut self, sub: &Subst) {
        match self {
            Type::Var(n) => {
                if let Some(t) = sub.0.get(n) {
                    *self = t.clone();
                }
            }
            Type::Lam(s, t) => {
                s.apply(sub);
                t.apply(sub);
            }
            _ => {}
        };
    }
}

impl Types for Scheme {
    fn apply(&mut self, sub: &Subst) {
        let mut s = sub.clone();

        for name in &self.0 {
            s.0.remove(name.deref());
        }

        self.1.apply(&s);
    }

    fn ftv(&self) -> Set<TypeVar> {
        let mut set = self.1.ftv();

        for var in &self.0 {
            set.remove(var.deref());
        }

        set
    }
}

impl<T: Types> Types for Vec<T> {
    fn ftv(&self) -> Set<TypeVar> {
        let mut set = Set::new();

        for t in self {
            for free in t.ftv() {
                set.insert(free);
            }
        }

        set
    }

    fn apply(&mut self, s: &Subst) {
        for t in self.iter_mut() {
            t.apply(s);
        }
    }
}

#[derive(Debug, Default)]
pub struct TIState {
    fresh: Fresh,
    ctx: Ctx,
    env: Env,
}

#[derive(Debug, Clone)]
pub enum UnificationError {
    IncombatibleTypes(String, String),
    OccursIn(TypeVar, String),
}

impl Display for UnificationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UnificationError::IncombatibleTypes(ty1, ty2) => {
                write!(f, "failed to unify {ty1} with {ty2}: unequal types")
            }
            UnificationError::OccursIn(s, ty) => {
                write!(f, "failed to unify '{s:#?} with {ty}: '{s} occurs in {ty}")
            }
        }
    }
}

impl TIState {
    pub fn env(&self) -> &Env {
        &self.env
    }

    fn unify(&mut self, ty1: &Type, ty2: &Type) -> Result<Subst, UnificationError> {
        match (ty1, ty2) {
            (Type::Lam(l, r), Type::Lam(l_, r_)) => {
                let s1 = self.unify(l, l_)?;

                let (mut r, mut r_) = (r.clone(), r_.clone());
                r.apply(&s1);
                r_.apply(&s1);

                let s2 = self.unify(&r, &r_)?;
                Ok(s1.compose(&s2))
            }
            (Type::Var(u), t) | (t, Type::Var(u)) => self.var_bind(*u, t),
            (Type::Adt(n), Type::Adt(m)) if n == m => Ok(Subst::null()),
            (ty1, ty2) => Err(UnificationError::IncombatibleTypes(
                format!("{}", TypePrinter(&self.env, &ty1)),
                format!("{}", TypePrinter(&self.env, &ty2)),
            )),
        }
    }

    fn var_bind(&self, var: TypeVar, ty: &Type) -> Result<Subst, UnificationError> {
        if let Type::Var(var_) = ty {
            if var == *var_ {
                return Ok(Subst::null());
            }
        }

        if ty.ftv().contains(&var) {
            return Err(UnificationError::OccursIn(
                var,
                format!("{}", TypePrinter(&self.env, ty)),
            ));
        }

        Ok(Subst::singleton(var, ty.clone()))
    }

    fn ti(&mut self, exp: &Rc<Spanned<Ast>>) -> Result<(Subst, Expr, Type), Report> {
        let savepoint = self.ctx.save();

        let res = || -> Result<(Subst, Expr, Type), Report> {
            let span = exp.deref().span();

            match exp.deref().deref() {
                Ast::Var(n) => self.ti_var(n, span),
                Ast::Lit(lit) => match lit {
                    Literal::Num(_) => Ok((Subst::null(), todo!(), Type::Prim(PrimType::Int))),
                },
                Ast::Abs(n, e) => self.ti_abs(n, e, span),
                Ast::App(e1, e2) => self.ti_app(e1, e2, span),
                Ast::Let(x, e1, e2) => self.ti_let(x, e1, e2, span),
                Ast::Match(name, arms) => self.ti_match(name, arms, span),
            }
        }();

        self.ctx.restore(savepoint);

        res
    }

    fn ti_var(&mut self, name: &Rc<str>, span: Span) -> Result<(Subst, Expr, Type), Report> {
        let (expr, r#type) = match self.ctx.get(name) {
            Some((expr, scheme)) => {
                let r#type = self.fresh.instantiate(scheme);

                let expr = match expr.cloned().or_else(|| self.env.lookup(name)) {
                    Some(expr) => expr,
                    None => {
                        panic!("name in env but can't find definition")
                    }
                };
                (expr, r#type)
            }
            None => {
                return Err(Report::build(ReportKind::Error, (), 0)
                    .with_label(
                        Label::new(span.into()).with_message(format!("unbound variable {name}")),
                    )
                    .finish())
            }
        };

        Ok((Subst::null(), expr, r#type))
    }

    fn ti_abs(
        &mut self,
        name: &Rc<str>,
        e: &Rc<Spanned<Ast>>,
        _: Span,
    ) -> Result<(Subst, Expr, Type), Report> {
        let mut tv = Type::Var(self.fresh.new_type_var());

        self.ctx.push_local(name.to_owned(), Box::new(tv.clone()));

        let (s1, e, t1) = self.ti(e)?;

        tv.apply(&s1);

        Ok((
            s1,
            Expr::Lam(Box::new(e)),
            Type::Lam(Box::new(tv), Box::new(t1)),
        ))
    }

    fn ti_app(
        &mut self,
        e1: &Rc<Spanned<Ast>>,
        e2: &Rc<Spanned<Ast>>,
        _: Span,
    ) -> Result<(Subst, Expr, Type), Report> {
        let mut tv = Type::Var(self.fresh.new_type_var());

        let (s1, e1_, mut t1) = self.ti(e1)?;

        self.ctx.apply(&s1);

        let (s2, e2_, t2) = self.ti(e2)?;

        t1.apply(&s2);

        let s3 = self
            .unify(&t1, &Type::Lam(Box::new(t2), Box::new(tv.clone())))
            .map_err(|err| {
                Report::build(ReportKind::Error, (), 0)
                    .with_label(Label::new(e1.span().into()).with_message(err.to_string()))
                    .finish()
            })?;
        tv.apply(&s3);

        Ok((
            s3.compose(&s2.compose(&s1)),
            Expr::App(Box::new(e1_), Box::new(e2_)),
            tv,
        ))
    }

    fn ti_let(
        &mut self,
        x: &Rc<str>,
        e1: &Rc<Spanned<Ast>>,
        e2: &Rc<Spanned<Ast>>,
        _: Span,
    ) -> Result<(Subst, Expr, Type), Report> {
        let (s1, mut e1, t1) = self.ti(e1)?;

        e1.convert_idx_to_lvl(self.ctx.level(), 0);

        self.ctx.apply(&s1);

        let t_ = self.ctx.generalize(&t1);

        self.ctx.push_let(x.clone(), e1, t_);
        self.ctx.apply(&s1);

        let (s2, e2, t2) = self.ti(e2)?;

        Ok((s1.compose(&s2), e2, t2))
    }

    fn ti_match(
        &mut self,
        name: &Spanned<Rc<str>>,
        arms: &Vec<Spanned<Clause>>,
        _: Span,
    ) -> Result<(Subst, Expr, Type), Report> {
        let (mut s, expr, mut input_ty) = self.ti_var(&name.0, name.span())?;

        let output_ty_var = self.fresh.new_type_var();
        let mut output_ty = Type::Var(output_ty_var);

        let mut ti_arms = std::iter::repeat_with(|| None)
            .take(arms.len())
            .collect::<Vec<_>>();

        for clause in arms {
            let (s_, clause_idx, expr) =
                self.ti_match_arm(&name.0, &mut input_ty, &mut output_ty, clause)?;

            ti_arms[clause_idx] = Some((clause.0.variables.len(), expr));

            self.ctx.apply(&s_);
            input_ty.apply(&s_);

            s = s_.compose(&s);
        }

        let aref = self
            .env
            .lookup_cons(arms[0].0.constructor.0.as_ref())
            .map(|cref| cref.0)
            .map_err(|err| {
                Report::build(ReportKind::Error, (), 0)
                    .with_label(
                        Label::new(arms[0].0.constructor.span().into())
                            .with_message(err.to_string()),
                    )
                    .finish()
            })?;

        output_ty.apply(&s);

        let span = arms.first().unwrap().span().start..arms.last().unwrap().span().end;

        let ti_arms = ti_arms
            .into_iter()
            .try_collect::<Vec<(usize, Expr)>>()
            .ok_or_else(|| {
                Report::build(ReportKind::Error, (), 0)
                    .with_label(Label::new(span))
                    .with_message("not all cases covered")
                    .finish()
            })?;

        Ok((s, Expr::Match(aref, Box::new(expr), ti_arms), output_ty))
    }

    fn ti_match_arm(
        &mut self,
        name: &Rc<str>,
        input: &mut Type,
        output: &mut Type,
        clause: &Clause,
    ) -> Result<(Subst, usize, Expr), Report> {
        let cons_ref = self
            .env
            .lookup_cons(clause.constructor.0.as_ref())
            .map_err(|err| {
                Report::build(ReportKind::Error, (), 0)
                    .with_label(
                        Label::new(clause.constructor.span().into()).with_message(err.to_string()),
                    )
                    .finish()
            })?;

        let s___ = self.unify(input, &Type::Adt(cons_ref.0)).map_err(|err| {
            Report::build(ReportKind::Error, (), 0)
                .with_message("failed to unify match variable with constructor in match arm")
                .with_label(
                    Label::new(clause.constructor.span().into()).with_message(err.to_string()),
                )
                .finish()
        })?;

        self.ctx.apply(&s___);
        input.apply(&s___);

        let s = self.unify(input, &Type::Adt(cons_ref.0)).map_err(|err| {
            Report::build(ReportKind::Error, (), 0)
                .with_message(err.to_string())
                .finish()
        })?;

        input.apply(&s);
        self.ctx.apply(&s);

        let cons = self.env.deref_cons(cons_ref);
        let num_cons_args = cons.arguments().len();

        if num_cons_args != clause.variables.len() {
            let span =
                clause.variables[0].span().start..clause.variables.last().unwrap().span().end;

            return Err(Report::build(ReportKind::Error, (), 0)
                .with_label(Label::new(span).with_message(format!(
                    "constructor takes {} arguments but {} arguments were given",
                    num_cons_args,
                    clause.variables.len()
                )))
                .finish());
        }

        let expr = clause.expr.clone();
        let savepoint = self.ctx.save();

        self.ctx.hide(name);
        for (ty, arg) in cons.arguments().iter().zip(clause.variables.iter()) {
            self.ctx.push_local(arg.0.clone(), Box::new(Type::Adt(*ty)));
        }

        let res = |this: &mut Self| -> Result<(Subst, usize, Expr), Report> {
            let (s__, expr, ty) = this.ti(&expr)?;
            this.ctx.apply(&s__);
            output.apply(&s__);

            let s_ = this.unify(&ty, output).map_err(|err| {
                Report::build(ReportKind::Error, (), 0)
                    .with_message(format!(
                        "failed to unify match arms with matched variable: {err}"
                    ))
                    .with_label(Label::new(
                        clause.constructor.span().start..clause.constructor.span().start,
                    ))
                    .finish()
            })?;

            this.ctx.apply(&s_);
            output.apply(&s_);
            input.apply(&s_);

            Ok((
                s__.compose(&s_.compose(&s.compose(&s___))),
                cons_ref.1,
                expr,
            ))
        }(self);

        self.ctx.restore(savepoint);

        res
    }

    pub fn check_adt(&mut self, def: AdtDef) -> Result<(), Report> {
        let mut names = Set::new();

        if !self.env.is_fresh(def.name.as_ref()) {
            let report = Report::build(ReportKind::Error, (), 0)
                .with_message(format!("identifier {} already taken", def.name))
                .finish();
            return Err(report);
        }

        names.insert(def.name.clone());

        for con in def.constructors.iter() {
            if !names.insert(con.name.clone()) || !self.env.is_fresh(&con.name) {
                let report = Report::build(ReportKind::Error, (), 0)
                    .with_message(format!("identifier {} already taken", def.name))
                    .finish();
                return Err(report);
            }

            for arg in con.arguments.iter().rev() {
                if arg.as_ref() != def.name.as_ref() && self.env.lookup_adt(arg).is_ok() {
                    let report = Report::build(ReportKind::Error, (), 0)
                        .with_message(format!(
                            "identifier {} not found or no algebraic data type",
                            def.name
                        ))
                        .finish();
                    return Err(report);
                }
            }
        }

        let adt_ref = self.env.insert_adt(def.clone()).unwrap();

        let mut cons = Vec::new();

        for (idx, con) in def.constructors.iter().enumerate() {
            let mut r#type = Type::Adt(adt_ref);

            let args: Vec<_> = con
                .arguments
                .iter()
                .map(|arg| self.env.lookup_adt(arg).unwrap())
                .collect();
            cons.push(Cons(ConsRef(adt_ref, idx), args));

            for arg in con.arguments.iter().rev() {
                if arg.as_ref() == def.name.as_ref() {
                    r#type = Type::Lam(Box::new(Type::Adt(adt_ref)), Box::new(r#type));
                } else {
                    r#type = Type::Lam(
                        Box::new(Type::Adt(self.env.lookup_adt(arg.as_ref()).unwrap())),
                        Box::new(r#type),
                    );
                }
            }

            self.ctx
                .insert_ty(con.name.clone(), Scheme(vec![], Box::new(r#type)));
        }

        self.env.adts.push(cons);

        Ok(())
    }

    pub fn check_exp(&mut self, expr: &Rc<Spanned<Ast>>) -> Result<(Expr, Type), Report> {
        let (subst, expr, mut ty) = self.ti(expr)?;
        ty.apply(&subst);

        Ok((expr, ty))
    }

    pub fn check_fun(&mut self, fun: FunctionDef) -> Result<Type, Report> {
        if !self.env.is_fresh(fun.name.as_ref()) {
            return Err(Report::build(ReportKind::Error, (), 0)
                .with_message(format!("{} already taken", fun.name))
                .finish());
        }

        let mut r#type = Type::Var(self.fresh.new_type_var());
        let mut body = fun.body.clone();

        for arg in fun.arguments.iter().rev() {
            r#type = Type::Lam(
                Box::new(Type::Var(self.fresh.new_type_var())),
                Box::new(r#type),
            );
            let span = body.span();
            body = Rc::new(Spanned(Ast::Abs(arg.clone(), body), span));
        }

        let savepoint = self.ctx.save();

        self.ctx
            .insert_ty(fun.name.clone(), Scheme(vec![], Box::new(r#type)));

        self.env
            .fun_map
            .insert(fun.name.clone(), FunRef(self.env.functions.len()));

        match self.ti(&body) {
            Ok((s, mut expr, mut ty)) => {
                ty.apply(&s);

                expr.convert_lvl_to_idx(0);

                self.ctx.restore(savepoint);

                self.ctx
                    .insert_ty(fun.name.clone(), self.ctx.generalize(&ty));

                self.env
                    .functions
                    .push((expr, ty.clone(), fun.name.clone()));

                Ok(ty)
            }
            Err(err) => {
                self.env.fun_map.remove(&fun.name);
                self.ctx.restore(savepoint);

                Err(err)
            }
        }
    }
}

#[derive(Clone, Default)]
pub struct Subst(pub Map<TypeVar, Type>);

impl Display for Subst {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut iter = self.0.iter();

        if let Some((key, value)) = iter.next() {
            write!(f, "{key}: {value:?}")?;
            for (key, value) in iter {
                write!(f, ", {key}: {value:?}")?;
            }
        }

        Ok(())
    }
}

impl std::fmt::Debug for Subst {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(self, f)
    }
}

impl Subst {
    pub fn null() -> Self {
        Self(Map::new())
    }

    pub fn singleton(x: TypeVar, t: Type) -> Self {
        let mut map = Map::new();
        map.insert(x, t);

        Self(map)
    }

    pub fn compose(&self, other: &Subst) -> Self {
        let mut subst = self.clone();

        for (x, y) in &other.0 {
            let mut y = y.clone();
            y.apply(self);

            subst.0.insert(*x, y);
        }

        subst
    }
}
