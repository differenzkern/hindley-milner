use std::collections::HashMap as Map;
use std::{fmt::Display, rc::Rc};

use ariadne::{Report, ReportKind, Source};
use check::{Namespace, TIState};
use type_env::TypeEnv;
use parser::Spanned;

use crate::check::{type_check, Scheme, Types};
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

    let toplevel = parse(&input);

    let mut namespace = Namespace(Map::new());

    let mut state = TIState::default();
    let mut env = TypeEnv::default();


    for toplevel in toplevel {
        let mut report = Report::build(ReportKind::Error, (), 0);

        match toplevel {
            Toplevel::Algebraic(def) => {
                let def = Rc::new(def);

                for (idx, con) in def.constructors.iter().enumerate() {
                    assert!(namespace
                        .insert(
                            con.name.clone(),
                            Name::Constructor {
                                idx,
                                r#type: def.clone()
                            }
                        )
                        .is_none());

                    let mut r#type = Type::Algebraic(def.name.clone());

                    for arg in con.arguments.iter().rev() {
                        r#type =
                            Type::Fun(Box::new(Type::Algebraic(arg.clone())), Box::new(r#type));
                    }

                    env.insert(con.name.clone(), Scheme(vec![], r#type));
                }

                assert!(namespace
                    .insert(def.name.clone(), Name::Type(def))
                    .is_none());
            }
            Toplevel::Fun(fun) => {
                let Function {
                    name,
                    body,
                    arguments,
                } = fun;

                let return_ty = state.new_type_var();

                let mut iter = arguments.iter().rev();

                let mut fun_ty = if arguments.len() > 0 {
                    let mut instantiate = |arg: &Rc<str>| {
                        let ty = state.new_type_var();
                        env.insert(arg.clone(), Scheme(vec![], ty.clone()));
                        ty
                    };

                    let mut fun_ty = Type::Fun(
                        Box::new(instantiate(iter.next().unwrap())),
                        Box::new(return_ty),
                    );

                    for arg in iter {
                        fun_ty = Type::Fun(Box::new(instantiate(arg)), Box::new(fun_ty));
                    }

                    fun_ty
                } else {
                    return_ty
                };

                env.insert(name, Scheme(vec![], fun_ty.clone()));

                let body = Rc::new(body);

                match state.ti(&namespace, &mut env, &body, &mut report, 0) {
                    Ok((mut s, mut ty)) => {
                        ty.apply(&s);

                        let s_ = state.unify(&fun_ty, &ty).unwrap();
                        s = s_.compose(&s);
                        fun_ty.apply(&s);

                        print!("fun");

                        for args in arguments {
                            print!(" {args}");
                        }

                        println!(" = {body}: {fun_ty}");


                    }
                    Err(_) => {
                        report.finish().print(Source::from(&input))?;
                    }
                }

                //assert!(namespace.insert(name, Name::Function(Rc::new(body))).is_none());
            }
            Toplevel::Expr(expr) => {
                let expr = Rc::new(expr);
                match type_check(&namespace, &expr, &mut env, &mut state, &mut report) {
                    Ok(ty) => {
                        println!("{expr}: {ty}");
                    }
                    Err(_) => {
                        report.finish().print(Source::from(&input))?;
                    }
                }
            }
        }
    }

    Ok(())
}

pub struct Names(Map<String, Name>);

pub enum Name {
    Constructor { idx: usize, r#type: Rc<Algebraic> },
    Function(Rc<Spanned<Expr>>),
    Type(Rc<Algebraic>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Toplevel {
    Algebraic(Algebraic),
    Fun(Function),
    Expr(Spanned<Expr>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Algebraic {
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
    body: Spanned<Expr>,
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
