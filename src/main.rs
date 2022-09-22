use std::fmt::Display;

use anyhow::Result;

use crate::check::typecheck;
use crate::parser::parse;

mod check;
mod parser;

fn main() -> Result<()> {
    let inputs = [
        "λx.let y = x in y",
        "(λx.x)(λy.y)",
        "3",
        "false",
        "λx.λy.x",
        "(λx.λy.x) false",
    ];

    for input in inputs {
        let expr = parse(input)?;
        let ty = typecheck(&expr)?;

        println!("{expr}: {ty}");
    }

    Ok(())
}

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
