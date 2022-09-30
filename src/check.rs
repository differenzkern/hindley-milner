use std::{
    collections::{HashMap as Map, HashSet as Set},
    fmt::Display,
    ops::{Deref, DerefMut, Range},
    rc::Rc,
};

use ariadne::{Label, ReportBuilder};

use crate::{parser::Spanned, Algebraic, Clause, Expr, Literal, Name, Type};

pub trait Types {
    fn ftv(&self) -> Set<String>;
    fn apply(&mut self, s: &Subst);
}

impl Types for Type {
    fn ftv(&self) -> Set<String> {
        match self {
            Type::Algebraic(_) => Set::new(),
            Type::Var(v) => [v.clone()].into(),
            Type::Int => Set::new(),
            Type::Bool => Set::new(),
            Type::Fun(x, y) => x.ftv().union(&y.ftv()).map(String::to_owned).collect(),
        }
    }

    fn apply(&mut self, sub: &Subst) {
        match self {
            Type::Var(n) => {
                if let Some(t) = sub.0.get(n) {
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
pub struct Scheme(pub Vec<String>, pub Type);

impl Display for Scheme {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !self.0.is_empty() {
            write!(f, "∀")?;

            for n in &self.0 {
                write!(f, " {n}")?;
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
            s.0.remove(name);
        }

        self.1.apply(&s);
    }

    fn ftv(&self) -> Set<String> {
        let mut set = self.1.ftv();

        for var in &self.0 {
            set.remove(var);
        }

        set
    }
}

impl<T: Types> Types for Vec<T> {
    fn ftv(&self) -> Set<String> {
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

#[derive(Debug, Clone)]
pub struct TypeEnv(pub Map<String, Scheme>);

impl Display for TypeEnv {
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

impl TypeEnv {
    pub fn remove(&mut self, var: &str) {
        self.0.remove(var);
    }

    pub fn generalize(&self, ty: &Type) -> Scheme {
        let mut vars = ty.ftv();

        for name in &self.ftv() {
            vars.remove(name);
        }

        Scheme(vars.into_iter().collect(), ty.clone())
    }
}

impl Types for TypeEnv {
    fn ftv(&self) -> Set<String> {
        self.0.values().cloned().collect::<Vec<Scheme>>().ftv()
    }

    fn apply(&mut self, s: &Subst) {
        for value in self.0.values_mut() {
            value.apply(s);
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct TIState(u64);

pub enum UnificationError {
    IncombatibleTypes(String, String),
    OccursIn(String, String),
}

impl Display for UnificationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UnificationError::IncombatibleTypes(ty1, ty2) => {
                write!(f, "failed to unify {ty1} with {ty2}: unequal types")
            }
            UnificationError::OccursIn(s, ty) => {
                write!(f, "failed to unify {s} with {ty}: {s} occurs in {ty}")
            }
        }
    }
}

impl TIState {
    pub fn new_type_var(&mut self, prefix: &str) -> Type {
        self.0 += 1;

        Type::Var(format!("{prefix}{}", self.0))
    }

    pub fn unify(&mut self, ty1: &Type, ty2: &Type) -> Result<Subst, UnificationError> {
        match (ty1, ty2) {
            (Type::Fun(l, r), Type::Fun(l_, r_)) => {
                let s1 = self.unify(l, l_)?;

                let (mut r, mut r_) = (r.clone(), r_.clone());
                r.apply(&s1);
                r_.apply(&s1);

                let s2 = self.unify(&r, &r_)?;
                Ok(s1.compose(&s2))
            }
            (Type::Var(u), t) | (t, Type::Var(u)) => self.var_bind(u, t),
            (Type::Int, Type::Int) => Ok(Subst::null()),
            (Type::Bool, Type::Bool) => Ok(Subst::null()),
            (Type::Algebraic(n), Type::Algebraic(m)) if n == m => Ok(Subst::null()),
            (ty1, ty2) => Err(UnificationError::IncombatibleTypes(
                ty1.to_string(),
                ty2.to_string(),
            )),
        }
    }

    pub fn var_bind(&self, s: &str, ty: &Type) -> Result<Subst, UnificationError> {
        if let Type::Var(var) = ty {
            if s == var {
                return Ok(Subst::null());
            }
        }

        if ty.ftv().contains(s) {
            return Err(UnificationError::OccursIn(s.to_string(), ty.to_string()));
        }

        Ok(Subst::singleton(s.to_owned(), ty.clone()))
    }

    pub fn instantiate(&mut self, scheme: &Scheme) -> Type {
        let mut map = Map::new();

        for var in &scheme.0 {
            let nvar = self.new_type_var("a");
            map.insert(var.clone(), nvar);
        }

        let mut t = scheme.1.clone();

        t.apply(&Subst(map));

        t
    }

    pub fn ti(
        &mut self,
        namespace: &Namespace,
        env: &TypeEnv,
        exp: &Rc<Spanned<Expr>>,
        report: &mut ReportBuilder<Range<usize>>,
        depth: u64,
    ) -> Result<(Subst, Type), ()> {
        let orig = env.clone();

        println!("{}>{env} ├ {exp}", " ".repeat(depth as usize));

        let span = exp.deref().1.clone();

        let (subst, t) = match exp.deref().deref() {
            Expr::Var(n) => match env.0.get(n) {
                Some(sigma) => {
                    let t = self.instantiate(sigma);
                    (Subst::null(), t)
                }
                None => match namespace.0.get(n) {
                    Some(n_) => match n_ {
                        Name::Constructor { r#type, .. } => {
                            (Subst::null(), Type::Algebraic(r#type.name.clone()))
                        }
                        Name::Function(body) => self.ti(namespace, env, body, report, depth + 1)?,
                        Name::Type(_) => {
                            report.add_label(Label::new(span).with_message(
                                "found type but expected variable, function or constructor",
                            ));
                            return Err(());
                        }
                    },
                    None => {
                        report.add_label(
                            Label::new(span).with_message(format!("unbound variable {n}")),
                        );
                        return Err(());
                    }
                },
            },
            Expr::Lit(lit) => match lit {
                Literal::Num(_) => (Subst::null(), Type::Int),
                Literal::Bool(_) => (Subst::null(), Type::Bool),
            },
            Expr::Abs(n, e) => {
                let mut tv = self.new_type_var("a");
                let mut env = env.clone();
                env.remove(n);
                env.0.insert(n.to_owned(), Scheme(vec![], tv.clone()));
                let (s1, t1) = self.ti(namespace, &env, e, report, depth + 1)?;
                tv.apply(&s1);

                (s1, Type::Fun(Box::new(tv), Box::new(t1)))
            }
            Expr::App(e1, e2) => {
                let mut tv = self.new_type_var("a");

                let (s1, mut t1) = self.ti(namespace, env, e1, report, depth + 1)?;

                let mut env = env.clone();
                env.apply(&s1);

                let (s2, t2) = self.ti(namespace, &env, e2, report, depth + 1)?;

                t1.apply(&s2);

                let s3 = self
                    .unify(&t1, &Type::Fun(Box::new(t2), Box::new(tv.clone())))
                    .map_err(|err| {
                        report.add_label(Label::new(e1.span()).with_message(err.to_string()));
                    })?;
                tv.apply(&s3);

                (s3.compose(&s2.compose(&s1)), tv)
            }
            Expr::Let(x, e1, e2) => {
                let (s1, t1) = self.ti(namespace, env, e1, report, depth + 1)?;

                let t_ = {
                    let mut env = env.clone();
                    env.apply(&s1);
                    env.generalize(&t1)
                };

                let mut env = env.clone();
                env.remove(x);
                env.0.insert(x.to_owned(), t_);
                env.apply(&s1);

                let (s2, t2) = self.ti(namespace, &env, e2, report, depth + 1)?;
                (s1.compose(&s2), t2)
            }
            Expr::Match(name, arms) => match env.0.get(&**name) {
                Some(ty) => {
                    let mut ty = self.instantiate(ty);

                    if arms.is_empty() {
                        report.add_label(Label::new(span.end..span.end));
                    }

                    let mut env_ = env.clone();

                    let matching_type = namespace
                        .expect_constructor(
                            &arms[0].constructor.0,
                            arms[0].constructor.span(),
                            report,
                        )
                        .unwrap()
                        .unwrap()
                        .1
                        .to_owned();

                    let mut s = self
                        .unify(&ty, &Type::Algebraic(matching_type.name.clone()))
                        .map_err(|err| {
                            report.add_label(Label::new(name.span()).with_message(err.to_string()))
                        })?;
                    env_.apply(&s);
                    ty.apply(&s);

                    //env_.remove(&name);

                    let (s_, mut ty) =
                        self.check_match_arm(namespace, &env_, &arms[0], report, depth)?;
                    env_.apply(&s_);
                    ty.apply(&s_);
                    s = s_.compose(&s);

                    for clause in &arms[1..] {
                        let (s_, ty_) =
                            self.check_match_arm(namespace, &env_, clause, report, depth)?;
                        env_.apply(&s_);
                        ty.apply(&s_);

                        s = s_.compose(&s);

                        let s_ =
                            self.unify(&ty, &ty_).map_err(|err| {
                                report.set_message(format!("failed to unify match arms: {err}"));
                                report.add_label(Label::new(clause.span()).with_message(
                                    "failed to unify this match arm with the previous",
                                ));
                            })?;
                        env_.apply(&s_);
                        ty.apply(&s_);

                        s = s_.compose(&s);
                    }

                    let mut coverage = Set::new();

                    for clause in arms {
                        let (idx, r#type) = namespace
                            .expect_constructor(&clause.constructor, clause.span(), report)
                            .unwrap()
                            .unwrap();

                        if &matching_type != r#type {
                            report.set_message("matched constructores have incompatible types");
                            report.add_label(
                                Label::new(arms[0].0.constructor.span())
                                    .with_message(format!("this has type {}", matching_type.name)),
                            );
                            report.add_label(
                                Label::new(clause.0.constructor.span())
                                    .with_message(format!("this has type {}", r#type.name)),
                            );

                            return Err(());
                        }

                        assert!(coverage.insert(idx));
                    }

                    if coverage.len() != matching_type.constructors.len() {
                        report.add_label(
                            Label::new(span).with_message("not all constructors covered"),
                        );

                        return Err(());
                    }

                    (s, ty)
                }
                None => {
                    report.add_label(Label::new(name.span()).with_message("unbound variable"));
                    return Err(());
                }
            },
        };

        println!(
            "{}<{orig} ├ {exp}: {t} ┤ {subst}",
            " ".repeat(depth as usize)
        );

        Ok((subst, t))
    }

    fn check_match_arm(
        &mut self,
        namespace: &Namespace,
        env: &TypeEnv,
        clause: &Clause,
        report: &mut ReportBuilder<Range<usize>>,
        depth: u64,
    ) -> Result<(Subst, Type), ()> {
        let (idx, r#type) = namespace
            .expect_constructor(&clause.constructor.0, clause.constructor.span(), report)?
            .ok_or_else(|| {
                report.add_label(
                    Label::new(clause.constructor.span()).with_message("constructor not found"),
                );
            })?;

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

        let mut env_ = env.clone();

        for (ty, name) in constructor.arguments.iter().zip(clause.variables.iter()) {
            env_.0.insert(
                name.0.to_owned(),
                Scheme(vec![], Type::Algebraic(ty.to_owned())),
            );
        }

        self.ti(namespace, env, &clause.expr, report, depth + 1)
    }
}

pub struct Namespace(pub Map<String, Name>);

impl Deref for Namespace {
    type Target = Map<String, Name>;

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
    ) -> Result<Option<(usize, &Rc<Algebraic>)>, ()> {
        match self.0.get(name.deref()) {
            Some(obj) => match obj {
                Name::Constructor { idx, r#type } => Ok(Some((*idx, r#type))),
                Name::Function(_) => {
                    report.add_label(
                        Label::new(span).with_message("expected constructor found function"),
                    );
                    Err(())
                }
                Name::Type(_) => {
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
pub struct Subst(Map<String, Type>);

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

    pub fn singleton(x: String, t: Type) -> Self {
        let mut map = Map::new();
        map.insert(x, t);

        Self(map)
    }

    pub fn compose(&self, other: &Subst) -> Self {
        let mut subst = self.clone();

        for (x, y) in &other.0 {
            let mut y = y.clone();
            y.apply(self);

            subst.0.insert(x.to_string(), y);
        }

        subst
    }
}

pub fn type_check(
    namespace: &Namespace,
    expr: &Rc<Spanned<Expr>>,
    env: &mut TypeEnv,
    state: &mut TIState,
    report: &mut ReportBuilder<Range<usize>>,
) -> Result<Type, ()> {
    let (subst, mut ty) = state.ti(namespace, env, expr, report, 0)?;
    ty.apply(&subst);

    Ok(ty)
}
