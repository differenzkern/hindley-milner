use std::collections::HashMap as Map;
use std::{fmt::Display, rc::Rc};

use ariadne::Source;
use check::TIState;
use chumsky::Parser;
use parse::ast::Toplevel;

use crate::parse::lexer::lexer;
use crate::parse::parse;
use crate::parse::ast::{Adt, Spanned, Expr};

pub mod parse;
pub mod check;
mod eval;
mod type_env;

#[macro_export]
macro_rules! cast {
    ($target: expr, $pat: path) => {
        {
            if let $pat(a) = $target { // #1
                a
            } else {
                panic!(
                    "mismatch variant when cast to {}", 
                    stringify!($pat)); // #2
            }
        }
    };
}



fn main() -> std::io::Result<()> {
    let args: Vec<String> = std::env::args().collect();

    if args.len() != 2 {
        println!("expected input file as argument");

        std::process::exit(-1);
    }

    let input = std::fs::read_to_string(&args.get(1).unwrap()).unwrap();

    dbg!(lexer().parse_recovery(input.as_str()));



    let toplevel = parse(input.as_str());

    let mut ti = TIState::default();

    for toplevel in toplevel {
        if let Err(report) = match toplevel {
            Toplevel::Adt(def) => ti.check_adt(Rc::from(def)),
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
    Constructor { idx: usize, r#type: Rc<Adt> },
    Function(Rc<Spanned<Expr>>),
    Adt(Rc<Adt>),
}


#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Algebraic(Rc<Adt>),
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
            Type::Algebraic(n) => n.name.fmt(f),
            Type::Var(n) => write!(f, "'{n}"),
            Type::Int => "int".fmt(f),
            Type::Fun(t, s) => {
                fmt_parens(t, f)?;
                write!(f, " → {s}")
            }
        }
    }
}

