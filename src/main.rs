use std::collections::HashMap as Map;
use std::{fmt::Display, rc::Rc};

use ariadne::Source;
use check::TIState;
use parser::Spanned;

use crate::parser::parse;

mod check;
mod parser;
mod type_env;

fn main() -> std::io::Result<()> {
    let args: Vec<String> = std::env::args().collect();

    if args.len() != 2 {
        println!("expected input file as argument");

        std::process::exit(-1);
    }

    let input = std::fs::read_to_string(&args.get(1).unwrap()).unwrap();

    let toplevel = parse(input.as_str());

    let mut ti = TIState::default();

    for toplevel in toplevel {
        if let Err(report) = match toplevel {
            Toplevel::ADT(def) => ti.check_adt(Rc::from(def)),
            Toplevel::Fun(fun) => match ti.check_fun(fun) {
                Ok(ty) => {
                    println!("{ty}");
                    Ok(())
                }
                Err(report) => Err(report),
            },
            Toplevel::Expr(expr) => match ti.check_exp(&Rc::new(expr)) {
                Ok(ty) => {
                    println!("{ty}");
                    Ok(())
                }
                Err(report) => Err(report),
            },
        } {
            report.eprint(Source::from(&input))?;
        }
    }

    Ok(())
}

pub struct Names(Map<String, Name>);

#[derive(Debug, Clone)]
pub enum Name {
    Constructor { idx: usize, r#type: Rc<ADT> },
    Function(Rc<Spanned<Expr>>),
    Type(Rc<ADT>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Toplevel {
    ADT(ADT),
    Fun(Function),
    Expr(Spanned<Expr>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ADT {
    name: Rc<str>,
    constructors: Vec<Constructor>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Constructor {
    name: Rc<str>,
    arguments: Vec<Rc<str>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Function {
    name: Rc<str>,
    arguments: Vec<Rc<str>>,
    body: Rc<Spanned<Expr>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Var(Rc<str>),
    App(Rc<Spanned<Expr>>, Rc<Spanned<Expr>>),
    Abs(Rc<str>, Rc<Spanned<Expr>>),
    Lit(Literal),
    Let(Rc<str>, Rc<Spanned<Expr>>, Rc<Spanned<Expr>>),
    Match(Spanned<Rc<str>>, Vec<Spanned<Clause>>),
}

#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Clause {
    constructor: Spanned<Rc<str>>,
    variables: Vec<Spanned<Rc<str>>>,
    expr: Rc<Spanned<Expr>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Literal {
    Num(u64),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Algebraic(Rc<str>),
    Var(usize),
    Int,
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
            Type::Algebraic(n) => n.fmt(f),
            Type::Var(n) => write!(f, "'{n}"),
            Type::Int => "int".fmt(f),
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

        write!(f, " | {constructor}")?;

        for var in variables {
            write!(f, " {var}")?;
        }

        write!(f, " → {expr}")
    }
}
