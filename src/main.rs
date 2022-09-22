use std::collections::HashMap as Map;
use std::collections::HashSet as Set;
use std::fmt::Display;

use anyhow::Result;

#[derive(Debug, Clone, PartialEq, Eq)]
enum Expr {
    Var(String),
    App(Box<Expr>, Box<Expr>),
    Abs(String, Box<Expr>),
    Lit(Literal),
    Let(String, Box<Expr>, Box<Expr>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Literal {
    Num(u64),
    Bool(bool),
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Type {
    Var(String),
    Int,
    Bool,
    Fun(Box<Type>, Box<Type>),
}

trait Types {
    fn ftv(&self) -> Set<String>;
    fn apply(&mut self, s: &Subst);
}

impl Types for Type {
    fn ftv(&self) -> Set<String> {
        match self {
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
struct Scheme(Vec<String>, Type);

impl Types for Scheme {
    fn apply(&mut self, s: &Subst) {
        let mut s = s.clone();

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
struct TypeEnv(Map<String, Scheme>);

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
struct TIState(u64);

impl TIState {
    pub fn new_type_var(&mut self, prefix: &str) -> Type {
        self.0 += 1;

        Type::Var(format!("{prefix}{}", self.0))
    }

    pub fn mgu(&mut self, t1: &Type, t2: &Type) -> Result<Subst> {
        match (t1, t2) {
            (Type::Fun(l, r), Type::Fun(l_, r_)) => {
                let s1 = self.mgu(l, l_)?;

                let (mut r, mut r_) = (r.clone(), r_.clone());
                r.apply(&s1);
                r_.apply(&s1);

                let s2 = self.mgu(&r, &r_)?;
                Ok(s1.compose(&s2))
            }
            (Type::Var(u), t) | (t, Type::Var(u)) => self.var_bind(u, t),
            (Type::Int, Type::Int) => Ok(Subst::null()),
            (Type::Bool, Type::Bool) => Ok(Subst::null()),
            (t1, t2) => anyhow::bail!("types do not unify: {t1} vs. {t2}"),
        }
    }

    pub fn var_bind(&self, s: &str, t: &Type) -> Result<Subst> {
        if let Type::Var(var) = t {
            if s == var {
                return Ok(Subst::null());
            }
        }

        if t.ftv().contains(s) {
            anyhow::bail!("occur check fails: {s} vs. {t}");
        }

        Ok(Subst::singleton(s.to_owned(), t.clone()))
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

    pub fn ti(&mut self, env: &TypeEnv, exp: Expr) -> Result<(Subst, Type)> {
        let (subst, t) = match exp {
            Expr::Var(n) => match env.0.get(&n) {
                Some(sigma) => {
                    let t = self.instantiate(sigma);
                    (Subst::null(), t)
                }
                None => anyhow::bail!("unbound variable {n}"),
            },
            Expr::Lit(lit) => match lit {
                Literal::Num(_) => (Subst::null(), Type::Int),
                Literal::Bool(_) => (Subst::null(), Type::Bool),
            },
            Expr::Abs(n, e) => {
                let mut tv = self.new_type_var("a");
                let mut env = env.clone();
                env.remove(&n);
                env.0.insert(n, Scheme(vec![], tv.clone()));
                let (s1, t1) = self.ti(&env, *e)?;
                tv.apply(&s1);

                (s1, Type::Fun(Box::new(tv), Box::new(t1)))
            }
            Expr::App(e1, e2) => {
                let mut tv = self.new_type_var("a");

                let (s1, mut t1) = self.ti(env, *e1)?;

                let mut env = env.clone();
                env.apply(&s1);

                let (s2, t2) = self.ti(&env, *e2)?;

                t1.apply(&s2);

                let s3 = self.mgu(&t1, &Type::Fun(Box::new(t2), Box::new(tv.clone())))?;
                tv.apply(&s3);

                (s3.compose(&s2.compose(&s1)), tv)
            }
            Expr::Let(x, e1, e2) => {
                let (s1, t1) = self.ti(env, *e1)?;

                let t_ = {
                    let mut env = env.clone();
                    env.apply(&s1);
                    env.generalize(&t1)
                };

                let mut env = env.clone();
                env.remove(&x);
                env.0.insert(x, t_);
                env.apply(&s1);

                let (s2, t2) = self.ti(&env, *e2)?;
                (s1.compose(&s2), t2)
            }
        };
        Ok((subst, t))
    }
}

#[derive(Clone, Default, Debug)]
struct Subst(Map<String, Type>);

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

fn main() -> Result<()> {
    let e0 = Expr::Let(
        "id".to_owned(),
        Box::new(Expr::Abs(
            "x".to_owned(),
            Box::new(Expr::Var("x".to_owned())),
        )),
        Box::new(Expr::Var("id".to_owned())),
    );

    let e1 = Expr::Let(
        "id".to_owned(),
        Box::new(Expr::Abs(
            "x".to_owned(),
            Box::new(Expr::Var("x".to_owned())),
        )),
        Box::new(Expr::App(
            Box::new(Expr::Var("id".to_owned())),
            Box::new(Expr::Var("id".to_owned())),
        )),
    );

    let e2 = Expr::Let(
        "id".to_owned(),
        Box::new(Expr::Abs(
            "x".to_owned(),
            Box::new(Expr::Let(
                "y".to_owned(),
                Box::new(Expr::Var("x".to_owned())),
                Box::new(Expr::Var("y".to_owned())),
            )),
        )),
        Box::new(Expr::App(
            Box::new(Expr::Var("id".to_owned())),
            Box::new(Expr::Var("id".to_owned())),
        )),
    );

    let e3 = Expr::Abs(
        "x".to_owned(),
        Box::new(Expr::Let(
            "y".to_owned(),
            Box::new(Expr::Var("x".to_owned())),
            Box::new(Expr::Var("y".to_owned())),
        )),
    );

    let expr = vec![e0, e1, e2, e3];

    for expr in expr {
        let mut state = TIState::default();
        let env = TypeEnv(Map::new());

        let (subst, mut ty) = state.ti(&env, expr.clone())?;
        ty.apply(&subst);

        println!("{expr}: {ty}\nS = {:?}\nΓ = {:?}\n", subst.0, env.0);
    }

    Ok(())
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn fmt_parens(this: &Type, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            if let Type::Fun(_, _) = this {
                write!(f, "({this})")
            } else {
                this.fmt(f)
            }
        }

        match self {
            Type::Var(n) => n.fmt(f),
            Type::Int => "int".fmt(f),
            Type::Bool => "bool".fmt(f),
            Type::Fun(t, s) => {
                fmt_parens(t, f)?;
                write!(f, " → {s}")
            }
        }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn fmt_parens(this: &Expr, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match this {
                this @ Expr::App(_, _) => write!(f, "({this})"),
                Expr::Abs(_, _) => write!(f, "({this})"),
                Expr::Let(_, _, _) => write!(f, "({this})"),
                _ => this.fmt(f),
            }
        }

        match self {
            Expr::Var(name) => write!(f, "{name}"),
            Expr::App(e1, e2) => {
                write!(f, "{e1} ")?;
                fmt_parens(e2, f)
            }
            Expr::Abs(x, e) => {
                write!(f, "λ{x}.")?;
                fmt_parens(e, f)
            }
            Expr::Lit(lit) => write!(f, "{lit}"),
            Expr::Let(x, e1, e2) => {
                write!(f, "let {x} = {e1} in {e2}")
            }
        }
    }
}

impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Literal::Num(x) => write!(f, "{x}"),
            Literal::Bool(x) => write!(f, "{x}"),
        }
    }
}
