use std::fmt::Display;

use anyhow::{Context, Result};

use crate::parser::parse;

mod check;
mod eval;
mod parser;

fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().collect();

    if args.len() != 2 {
        anyhow::bail!("expected input file argument");
    }

    let input = std::fs::read_to_string(&args[1]).context("failed to read file")?;

    let toplevel = parse(&input).context("failed to parse file")?;

    dbg!(toplevel);

    Ok(())
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Toplevel {
    Ind(Inductive),
    Fun(Function),
    Expr(Expr),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Inductive {
    name: String,
    constructors: Vec<Constructor>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Constructor {
    name: String,
    arguments: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Function {
    name: String,
    arguments: Vec<String>,
    body: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Var(String),
    App(Box<Expr>, Box<Expr>),
    Abs(String, Box<Expr>),
    Lit(Literal),
    Let(String, Box<Expr>, Box<Expr>),
    Match(String, Vec<Clause>),
}

#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Clause {
    constructor: String,
    variables: Vec<String>,
    expr: Expr,
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
            Expr::Match(x, clauses) => {
                write!(f, "match {x}")?;
                for clause in clauses {
                    write!(f, "{clause}")?;
                }
                Ok(())
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

impl Display for Clause {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Clause {
            constructor,
            variables,
            expr,
        } = self;

        write!(f, "| {constructor}")?;

        for var in variables {
            write!(f, " {var}")?;
        }

        write!(f, " → {expr}")
    }
}
