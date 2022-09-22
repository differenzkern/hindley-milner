use std::fmt::Display;

use anyhow::Result;

use crate::check::typecheck;

mod check;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Var(String),
    App(Box<Expr>, Box<Expr>),
    Abs(String, Box<Expr>),
    Lit(Literal),
    Let(String, Box<Expr>, Box<Expr>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Literal {
    Num(u64),
    Bool(bool),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Var(String),
    Int,
    Bool,
    Fun(Box<Type>, Box<Type>),
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
        println!("{expr}: {}\n", typecheck(&expr)?);
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
