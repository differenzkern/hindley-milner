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
    env::{DefType, Env},
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

impl Types for Scheme<Type> {
    fn apply(&mut self, sub: &Subst) {
        let mut s = sub.clone();

        if let Some(vars) = &self.0 {
            for name in vars {
                s.0.remove(name.deref());
            }
        }

        self.1.apply(&s);
    }

    fn ftv(&self) -> Set<TypeVar> {
        let mut set = self.1.ftv();

        if let Some(vars) = &self.0 {
            for var in vars {
                set.remove(var);
            }
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

    check_fun: Option<(Rc<str>, FunRef)>,
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

    fn ti(
        &mut self,
        exp: &Rc<Spanned<Ast>>,
        lvl: usize,
    ) -> Result<(Subst, Rc<Expr>, Type), Report> {
        let savepoint = self.ctx.save();

        let res = || -> Result<(Subst, Rc<Expr>, Type), Report> {
            let span = exp.deref().span();

            match exp.deref().deref() {
                Ast::Var(n) => self.ti_var(n, span, lvl),
                Ast::Lit(lit) => match lit {
                    Literal::Num(_) => Ok((Subst::null(), todo!(), Type::Prim(PrimType::Int))),
                },
                Ast::Abs(n, e) => self.ti_abs(n, e, span, lvl + 1),
                Ast::App(e1, e2) => self.ti_app(e1, e2, span, lvl),
                Ast::Let(x, e1, e2) => self.ti_let(x, e1, e2, span, lvl),
                Ast::Match(name, arms) => self.ti_match(name, arms, span, lvl),
            }
        }();

        self.ctx.restore(savepoint);

        res
    }

    fn ti_var(
        &mut self,
        name: &Rc<str>,
        span: Span,
        lvl: usize,
    ) -> Result<(Subst, Rc<Expr>, Type), Report> {
        let (expr, r#type) = self
            .ctx
            .get(name, lvl)
            .and_then(|(expr, ty)| {
                expr.map(|expr| (expr, ty))
                    .or_else(|| match &self.check_fun {
                        Some((name_, fref)) if name_ == name => Some((Rc::new(Expr::Fun(*fref)), ty)),
                        _ => None,
                    })
            })
            .or_else(|| {
                self.env
                    .lookup(name)
                    .map(|(_, expr, ty)| (expr.clone(), ty))
            })
            .ok_or_else(|| {
                Report::build(ReportKind::Error, (), 0)
                    .with_label(
                        Label::new(span.into()).with_message(format!("unbound variable {name}")),
                    )
                    .finish()
            })?;

        Ok((Subst::null(), expr.clone(), self.fresh.instantiate(r#type)))
    }

    fn ti_abs(
        &mut self,
        name: &Rc<str>,
        e: &Rc<Spanned<Ast>>,
        _: Span,
        lvl: usize,
    ) -> Result<(Subst, Rc<Expr>, Type), Report> {
        let mut tv = Type::Var(self.fresh.new_type_var());

        self.ctx.push_local(name.to_owned(), tv.clone());

        let (s1, e, t1) = self.ti(e, lvl)?;

        tv.apply(&s1);

        Ok((
            s1,
            Rc::new(Expr::Lam(e)),
            Type::Lam(Box::new(tv), Box::new(t1)),
        ))
    }

    fn ti_app(
        &mut self,
        e1: &Rc<Spanned<Ast>>,
        e2: &Rc<Spanned<Ast>>,
        _: Span,
        lvl: usize,
    ) -> Result<(Subst, Rc<Expr>, Type), Report> {
        let mut tv = Type::Var(self.fresh.new_type_var());

        let (s1, e1_, mut t1) = self.ti(e1, lvl)?;

        self.ctx.apply(&s1);

        let (s2, e2_, t2) = self.ti(e2, lvl)?;

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
            Rc::new(Expr::App(e1_, e2_)),
            tv,
        ))
    }

    fn ti_let(
        &mut self,
        x: &Rc<str>,
        e1: &Rc<Spanned<Ast>>,
        e2: &Rc<Spanned<Ast>>,
        _: Span,
        lvl: usize,
    ) -> Result<(Subst, Rc<Expr>, Type), Report> {
        let (s1, mut e1, t1) = self.ti(e1, lvl)?;

        //e1.convert_idx_to_lvl(self.ctx.level(), 0);

        self.ctx.apply(&s1);

        let t_ = self.ctx.generalize(&t1);

        self.ctx.push_let(x.clone(), e1, t_);
        self.ctx.apply(&s1);

        let (s2, e2, t2) = self.ti(e2, lvl)?;

        Ok((s1.compose(&s2), e2, t2))
    }

    fn ti_match(
        &mut self,
        name: &Spanned<Rc<str>>,
        arms: &Vec<Spanned<Clause>>,
        _: Span,
        lvl: usize,
    ) -> Result<(Subst, Rc<Expr>, Type), Report> {
        let (mut s, expr, mut input_ty) = self.ti_var(&name.0, name.span(), lvl)?;

        let output_ty_var = self.fresh.new_type_var();
        let mut output_ty = Type::Var(output_ty_var);

        let mut ti_arms = std::iter::repeat_with(|| None)
            .take(arms.len())
            .collect::<Vec<_>>();

        for clause in arms {
            let (s_, clause_idx, expr) =
                self.ti_match_arm(&name.0, &mut input_ty, &mut output_ty, clause, lvl)?;

            ti_arms[clause_idx] = Some((clause.0.variables.len(), expr));

            self.ctx.apply(&s_);
            input_ty.apply(&s_);

            s = s_.compose(&s);
        }

        let cref = self
            .env
            .lookup_cons(arms[0].0.constructor.0.as_ref())
            .map_err(|err| {
                Report::build(ReportKind::Error, (), 0)
                    .with_label(
                        Label::new(arms[0].0.constructor.span().into())
                            .with_message("expected algebraic data type"),
                    )
                    .finish()
            })?;

        output_ty.apply(&s);

        let span = arms.first().unwrap().span().start..arms.last().unwrap().span().end;

        let ti_arms = ti_arms
            .into_iter()
            .try_collect::<Vec<(usize, Rc<Expr>)>>()
            .ok_or_else(|| {
                Report::build(ReportKind::Error, (), 0)
                    .with_label(Label::new(span))
                    .with_message("not all cases covered")
                    .finish()
            })?;

        Ok((s, Rc::new(Expr::Match(cref.0, expr, ti_arms)), output_ty))
    }

    fn ti_match_arm(
        &mut self,
        name: &Rc<str>,
        input: &mut Type,
        output: &mut Type,
        clause: &Clause,
        lvl: usize,
    ) -> Result<(Subst, usize, Rc<Expr>), Report> {
        let cons_ref = self
            .env
            .lookup_cons(clause.constructor.0.as_ref())
            .map_err(|err| {
                Report::build(ReportKind::Error, (), 0)
                    .with_label(
                        Label::new(clause.constructor.span().into())
                            .with_message(format!("unknown constructor {name}")),
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

        let cons = &self.env.get_cons(cons_ref).1;

        let num_cons_args = cons.1.len();

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
        for (ty, arg) in cons.1.iter().zip(clause.variables.iter()) {
            self.ctx.push_local(arg.0.clone(), Type::Adt(*ty));
        }

        let lvl = lvl + cons.arguments().len();

        let res = |this: &mut Self| -> Result<(Subst, usize, Rc<Expr>), Report> {
            let (s__, expr, ty) = this.ti(&expr, lvl)?;
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
                if arg.as_ref() != def.name.as_ref() && self.env.lookup(arg).is_some() {
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

        self.env.insert_adt(def.clone());
        Ok(())
    }

    pub fn check_exp(&mut self, expr: &Rc<Spanned<Ast>>) -> Result<(Rc<Expr>, Type), Report> {
        let (subst, mut expr, mut ty) = self.ti(expr, 0)?;
        ty.apply(&subst);
        //expr.convert_lvl_to_idx(0);

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

        self.check_fun = Some((fun.name.clone(), self.env.next_fun()));

        self.ctx
            .types
            .insert(fun.name.clone(), Scheme(None, r#type));

        match self.ti(&body, 0) {
            Ok((s, mut expr, mut ty)) => {
                ty.apply(&s);

                //expr.convert_lvl_to_idx(0);

                self.ctx.restore(savepoint);

                self.check_fun = None;

                dbg!(&expr);

                self.env
                    .insert_fun(fun.name.clone(), expr, self.ctx.generalize(&ty));

                Ok(ty)
            }
            Err(err) => {
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
