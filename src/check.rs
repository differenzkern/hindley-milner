use std::{
    collections::{HashMap as Map, HashSet as Set},
    fmt::Display,
    ops::{Deref, DerefMut, Range},
    rc::Rc,
};

use ariadne::{Label, Report, ReportBuilder, ReportKind};

use crate::{type_env::TypeEnv, Name, Type, cast};
use crate::parse::ast::{Clause, Expr, Function, Literal, Adt, Spanned};

pub trait Types {
    fn ftv(&self) -> Set<usize>;
    fn apply(&mut self, s: &Subst);
}

impl Types for Type {
    fn ftv(&self) -> Set<usize> {
        match self {
            Type::Algebraic(_) => Set::new(),
            Type::Var(v) => [*v].into(),
            Type::Int => Set::new(),
            Type::Fun(x, y) => x.ftv().union(&y.ftv()).copied().collect(),
        }
    }

    fn apply(&mut self, sub: &Subst) {
        match self {
            Type::Var(n) => {
                if let Some(t) = sub.0.get(n.deref()) {
                    *self = t.clone();
                }
            }
            Type::Fun(s, t) => {
                s.apply(sub);
                t.apply(sub);
            }
            _ => {}
        };
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Scheme(pub Vec<usize>, pub Type);

impl Display for Scheme {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !self.0.is_empty() {
            write!(f, "∀")?;

            for n in &self.0 {
                write!(f, " '{n}")?;
            }

            write!(f, ".")?;
        }

        write!(f, "{}", self.1)
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

    fn ftv(&self) -> Set<usize> {
        let mut set = self.1.ftv();

        for var in &self.0 {
            set.remove(var.deref());
        }

        set
    }
}

impl<T: Types> Types for Vec<T> {
    fn ftv(&self) -> Set<usize> {
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

#[derive(Debug, Clone, Default)]
pub struct TIState {
    fresh: Fresh,
    env: TypeEnv,
    namespace: Namespace,
}

#[derive(Debug, Clone, Default)]
pub struct Fresh(usize);

impl Fresh {
    fn instantiate(&mut self, scheme: &Scheme) -> Type {
        let mut map = Map::new();

        for var in &scheme.0 {
            let nvar = self.new_type_var();
            map.insert(*var, nvar);
        }

        let mut t = scheme.1.clone();

        t.apply(&Subst(map));

        t
    }

    fn new_type_var(&mut self) -> Type {
        self.0 += 1;

        Type::Var(self.0 - 1)
    }
}

#[derive(Debug, Clone)]
pub enum UnificationError {
    IncombatibleTypes(String, String),
    OccursIn(usize, String),
}

impl Display for UnificationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UnificationError::IncombatibleTypes(ty1, ty2) => {
                write!(f, "failed to unify {ty1} with {ty2}: unequal types")
            }
            UnificationError::OccursIn(s, ty) => {
                write!(f, "failed to unify '{s} with {ty}: '{s} occurs in {ty}")
            }
        }
    }
}

impl TIState {
    fn unify(&mut self, ty1: &Type, ty2: &Type) -> Result<Subst, UnificationError> {
        match (ty1, ty2) {
            (Type::Fun(l, r), Type::Fun(l_, r_)) => {
                let s1 = self.unify(l, l_)?;

                let (mut r, mut r_) = (r.clone(), r_.clone());
                r.apply(&s1);
                r_.apply(&s1);

                let s2 = self.unify(&r, &r_)?;
                Ok(s1.compose(&s2))
            }
            (Type::Var(u), t) | (t, Type::Var(u)) => self.var_bind(*u, t),
            (Type::Int, Type::Int) => Ok(Subst::null()),
            (Type::Algebraic(n), Type::Algebraic(m)) if n == m => Ok(Subst::null()),
            (ty1, ty2) => Err(UnificationError::IncombatibleTypes(
                ty1.to_string(),
                ty2.to_string(),
            )),
        }
    }

    fn var_bind(&self, var: usize, ty: &Type) -> Result<Subst, UnificationError> {
        if let Type::Var(var_) = ty {
            if var == *var_ {
                return Ok(Subst::null());
            }
        }

        if ty.ftv().contains(&var) {
            return Err(UnificationError::OccursIn(var, ty.to_string()));
        }

        Ok(Subst::singleton(var, ty.clone()))
    }

    fn ti(
        &mut self,
        exp: &Rc<Spanned<Expr>>,
        report: &mut ReportBuilder<Range<usize>>,
        depth: u64,
    ) -> Result<(Subst, Type), ()> {
        let savepoint = self.env.savepoint();

        let res = || -> Result<(Subst, Type), ()> {
            let span = exp.deref().1.clone();

            match exp.deref().deref() {
                Expr::Var(n) => match self.env.get(n) {
                    Some(sigma) => {
                        let t = self.fresh.instantiate(sigma);
                        Ok((Subst::null(), t))
                    }
                    None => {
                        report.add_label(
                            Label::new(span.into()).with_message(format!("unbound variable {n}")),
                        );
                        Err(())
                    }
                },
                Expr::Lit(lit) => match lit {
                    Literal::Num(_) => Ok((Subst::null(), Type::Int)),
                },
                Expr::Abs(n, e) => {
                    let mut tv = self.fresh.new_type_var();
                    self.env.insert(n.to_owned(), Scheme(vec![], tv.clone()));
                    let (s1, t1) = self.ti(e, report, depth + 1)?;
                    tv.apply(&s1);

                    Ok((s1, Type::Fun(Box::new(tv), Box::new(t1))))
                }
                Expr::App(e1, e2) => {
                    let mut tv = self.fresh.new_type_var();

                    let (s1, mut t1) = self.ti(e1, report, depth + 1)?;

                    self.env.apply(&s1);

                    let (s2, t2) = self.ti(e2, report, depth + 1)?;

                    t1.apply(&s2);

                    let s3 = self
                        .unify(&t1, &Type::Fun(Box::new(t2), Box::new(tv.clone())))
                        .map_err(|err| {
                            report.add_label(Label::new(e1.span().into()).with_message(err.to_string()));
                        })?;
                    tv.apply(&s3);

                    Ok((s3.compose(&s2.compose(&s1)), tv))
                }
                Expr::Let(x, e1, e2) => {
                    let (s1, t1) = self.ti(e1, report, depth + 1)?;

                    let t_ = {
                        let mut env = self.env.clone();
                        env.apply(&s1);
                        env.generalize(&t1)
                    };

                    self.env.insert(x.to_owned(), t_);
                    self.env.apply(&s1);

                    let (s2, t2) = self.ti(e2, report, depth + 1)?;
                    Ok((s1.compose(&s2), t2))
                }
                Expr::Match(name, arms) => {
                    let mut input_ty = match self.env.get(&**name) {
                        Some(ty) => self.fresh.instantiate(ty),
                        None => {
                            report.add_label(
                                Label::new(name.span().into()).with_message("unbound variable"),
                            );
                            return Err(());
                        }
                    };
                    let mut output_ty = self.fresh.new_type_var();

                    self.env.remove(name);

                    let mut s = Subst::null();

                    for clause in arms {
                        let (s_, ty_) =
                            self.check_match_arm(&mut input_ty, clause, report, depth)?;

                        self.env.apply(&s_);
                        input_ty.apply(&s_);
                        output_ty.apply(&s_);

                        s = s_.compose(&s);

                        let s_ =
                            self.unify(&output_ty, &ty_).map_err(|err| {
                                report.set_message(format!("failed to unify match arms: {err}"));
                                report.add_label(Label::new(clause.span().into()).with_message(
                                    "failed to unify this match arm with the previous",
                                ));
                            })?;

                        self.env.apply(&s_);
                        input_ty.apply(&s_);
                        output_ty.apply(&s_);

                        s = s_.compose(&s);
                    }

                    Ok((s, output_ty))
                }
            }
        }();

        self.env.restore(savepoint);

        res
    }

    fn check_match_arm(
        &mut self,
        input: &mut Type,
        clause: &Clause,
        report: &mut ReportBuilder<Range<usize>>,
        depth: u64,
    ) -> Result<(Subst, Type), ()> {
        let savepoint = self.env.savepoint();

        let (idx, r#type) = self
            .namespace
            .expect_constructor(&clause.constructor.0, clause.constructor.span().into(), report)?
            .ok_or_else(|| {
                report.add_label(
                    Label::new(clause.constructor.span().into()).with_message("constructor not found"),
                );
            })?;

        let r#type = r#type.to_owned();

        let constructor = &r#type.constructors[idx];

        if constructor.arguments.len() != clause.variables.len() {
            let span =
                clause.variables[0].span().start..clause.variables.last().unwrap().span().end;

            report.add_label(Label::new(span).with_message(format!(
                "constructor takes {} arguments but {} arguments were given",
                constructor.arguments.len(),
                clause.variables.len()
            )));

            return Err(());
        }

        let s = self
            .unify(input, &Type::Algebraic(r#type.clone()))
            .map_err(|err| {
                report.set_message(format!(
                    "failed to unify match arms with matched variable: {err}"
                ));
                report.add_label(Label::new(
                    clause.constructor.span().start..clause.constructor.span().start,
                ));
            })?;

        input.apply(&s);
        self.env.apply(&s);

        for (ty, name) in constructor.arguments.iter().zip(clause.variables.iter()) {
            let ty = cast!(self.namespace.0.get(name.deref()).unwrap(), Name::Adt);

            self.env.insert(
                name.0.clone(),
                Scheme(vec![], Type::Algebraic(ty.clone())),
            );
        }

        match self.ti(&clause.expr, report, depth + 1) {
            Ok((s_, ty)) => Ok((s.compose(&s_), ty)),
            Err(err) => {
                self.env.restore(savepoint);
                Err(err)
            }
        }
    }

    pub fn check_adt(&mut self, def: Rc<Adt>) -> Result<(), Report> {
        for (idx, con) in def.constructors.iter().enumerate() {
            assert!(self
                .namespace
                .insert(
                    con.name.clone(),
                    Name::Constructor {
                        idx,
                        r#type: def.clone()
                    }
                )
                .is_none());

            let mut r#type = Type::Algebraic(def.clone());

            for arg in con.arguments.iter().rev() {
                r#type = Type::Fun(Box::new(Type::Algebraic(cast!(self.namespace.0.get(arg).unwrap(), Name::Adt).clone())), Box::new(r#type));
            }

            self.env.insert(con.name.clone(), Scheme(vec![], r#type));
        }

        assert!(self
            .namespace
            .insert(def.name.clone(), Name::Adt(def))
            .is_none());

        Ok(())
    }

    pub fn check_exp(&mut self, expr: &Rc<Spanned<Expr>>) -> Result<Type, Report> {
        let savepoint = self.env.savepoint();
        let mut report = Report::build(ReportKind::Error, (), 0);

        let res = || -> Result<Type, ()> {
            let (subst, mut ty) = self.ti(expr, &mut report, 0)?;
            ty.apply(&subst);
            Ok(ty)
        }();

        self.env.restore(savepoint);

        match res {
            Ok(res) => Ok(res),
            Err(_) => Err(report.finish()),
        }
    }

    pub fn check_fun(&mut self, fun: Function) -> Result<Type, Report> {
        let savepoint = self.env.savepoint();
        let mut report = Report::build(ReportKind::Error, (), 0);

        let res = || -> Result<Type, ()> {
            let Function {
                name,
                body,
                arguments,
            } = &fun;

            let return_ty = self.fresh.new_type_var();

            let mut iter = arguments.iter().rev();

            let mut fun_ty = if !arguments.is_empty() {
                let mut instantiate = |arg: &Rc<str>| {
                    let ty = self.fresh.new_type_var();
                    self.env.insert(arg.clone(), Scheme(vec![], ty.clone()));
                    ty
                };

                let mut fun_ty = Type::Fun(
                    Box::new(instantiate(iter.next().unwrap())),
                    Box::new(return_ty.clone()),
                );

                for arg in iter {
                    fun_ty = Type::Fun(Box::new(instantiate(arg)), Box::new(fun_ty));
                }

                fun_ty
            } else {
                return_ty.clone()
            };

            self.env
                .insert(name.clone(), Scheme(vec![], fun_ty.clone()));

            let body = Rc::new(body.to_owned());

            match self.ti(&body, &mut report, 0) {
                Ok((s, mut ty)) => {
                    ty.apply(&s);
                    fun_ty.apply(&s);

                    let s_ = self.unify(&return_ty, &ty).map_err(|err| {
                        report.add_label(Label::new(body.span().into()).with_message(err.to_string()));
                    })?;

                    fun_ty.apply(&s_);

                    Ok(fun_ty)
                }
                Err(_) => Err(()),
            }
        }();

        self.env.restore(savepoint);

        if let Ok(ty) = &res {
            self.env.insert(fun.name.clone(), self.env.generalize(ty));
        }

        match res {
            Ok(ty) => Ok(ty),
            Err(_) => Err(report.finish()),
        }
    }
}

#[derive(Debug, Default, Clone)]
pub struct Namespace(pub Map<Rc<str>, Name>);

impl Deref for Namespace {
    type Target = Map<Rc<str>, Name>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Namespace {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl Namespace {
    pub fn expect_constructor(
        &self,
        name: &str,
        span: Range<usize>,
        report: &mut ReportBuilder<Range<usize>>,
    ) -> Result<Option<(usize, &Rc<Adt>)>, ()> {
        match self.0.get(name.deref()) {
            Some(obj) => match obj {
                Name::Constructor { idx, r#type } => Ok(Some((*idx, r#type))),
                Name::Function(_) => {
                    report.add_label(
                        Label::new(span).with_message("expected constructor found function"),
                    );
                    Err(())
                }
                Name::Adt(_) => {
                    report.add_label(
                        Label::new(span).with_message("expected constructor found type"),
                    );
                    Err(())
                }
            },
            None => Ok(None),
        }
    }
}

#[derive(Clone, Default)]
pub struct Subst(Map<usize, Type>);

impl Display for Subst {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut iter = self.0.iter();

        if let Some((key, value)) = iter.next() {
            write!(f, "{key}: {value}")?;
            for (key, value) in iter {
                write!(f, ", {key}: {value}")?;
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

    pub fn singleton(x: usize, t: Type) -> Self {
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
