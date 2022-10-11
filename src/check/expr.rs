use std::{rc::Rc, borrow::Cow};

use crate::check::env::ExprPrinter;

use super::{env::Env, r#type::Type};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ConsRef(pub AdtRef, pub usize);

impl From<ConsRef> for AdtRef {
    fn from(cons_ref: ConsRef) -> Self {
        cons_ref.0
    }
}

impl From<&ConsRef> for AdtRef {
    fn from(cons_ref: &ConsRef) -> Self {
        cons_ref.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FunRef(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AdtRef(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Name {
    Cons(ConsRef),
    Fun(FunRef),
    Adt(AdtRef),
}

#[derive(Debug, Clone)]
pub enum EnvError<'a> {
    SymbolNotFound(&'a str),
    NotAFunction { name: Rc<str> },
    NotAType { name: &'a str },
    NotACons { name: &'a str },
}

impl<'a> std::fmt::Display for EnvError<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EnvError::SymbolNotFound(name) => {
                write!(f, "could not find symbol {name} in environment")
            }
            EnvError::NotAFunction { name } => write!(f, "{name} is not a function"),
            EnvError::NotAType { name } => write!(f, "{name} is not a type"),
            EnvError::NotACons { name } => write!(f, "{name} is not a constructor"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    /// lambda application
    App(Box<Expr>, Box<Expr>),
    /// application of constructor
    ConsApp(ConsRef, Vec<Expr>),
    DeBrujinIdx(usize),
    DeBrujinLvl(usize),
    Lam(Box<Expr>),
    Match(AdtRef, Box<Expr>, Vec<(usize, Expr)>),
    Fun(FunRef),
}

impl Expr {
    pub fn convert_lvl_to_idx(&mut self, level: usize) {
        match self {
            Expr::App(e1, e2) => {
                e1.convert_lvl_to_idx(level);
                e2.convert_lvl_to_idx(level);
            }
            Expr::ConsApp(_, e2) => {
                e2.iter_mut().for_each(|e| e.convert_lvl_to_idx(level));
            }
            Expr::DeBrujinLvl(lvl) => {
                *self = Expr::DeBrujinIdx(level - 1 - *lvl);
            }
            Expr::Lam(expr) => expr.convert_lvl_to_idx(level + 1),
            Expr::Match(_, e1, e2) => {
                e1.convert_lvl_to_idx(level);
                e2.iter_mut()
                    .for_each(|(args, e)| e.convert_lvl_to_idx(level + *args));
            }
            _ => {}
        }
    }

    pub fn convert_idx_to_lvl(&mut self, level: usize, max_idx: usize) {
        match self {
            Expr::App(e1, e2) => {
                e1.convert_idx_to_lvl(level, max_idx);
                e2.convert_idx_to_lvl(level, max_idx);
            }
            Expr::ConsApp(_, e2) => {
                e2.iter_mut()
                    .for_each(|e| e.convert_idx_to_lvl(level, max_idx));
            }
            Expr::DeBrujinIdx(idx) => {
                if *idx >= max_idx {
                    *self = Expr::DeBrujinLvl(level - 1 - *idx);
                }
            }
            Expr::Lam(e) => {
                e.convert_idx_to_lvl(level + 1, max_idx + 1);
            }
            Expr::Match(_, e1, e2) => {
                e1.convert_idx_to_lvl(level, max_idx);
                e2.iter_mut()
                    .for_each(|(args, e)| e.convert_idx_to_lvl(level + *args, max_idx));
            }
            _ => {}
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DeBrujin(usize);

#[derive(Debug, Clone)]
pub struct Cons(pub ConsRef, pub Vec<AdtRef>);

impl Cons {
    pub fn cons_ref(&self) -> ConsRef {
        self.0
    }

    pub fn arguments(&self) -> &Vec<AdtRef> {
        &self.1
    }
}

#[derive(Debug)]
enum Sem {
    Lam(Rc<Vec<Rc<Sem>>>, Box<Expr>),
    ConsApp(ConsRef, Vec<Rc<Sem>>),
    Syn(Box<Expr>),
}

pub struct EvalContext {
    env: Env,
}

impl EvalContext {
    pub fn new(env: Env) -> Self {
        Self { env }
    }

    fn meaning(&self, tm: &Expr, ctx: &Vec<Rc<Sem>>) -> Rc<Sem> {
        match tm {
            Expr::App(s, t) => {
                if let Sem::Lam(ctx_, tm) = self.meaning(s, ctx).as_ref() {
                    let mut ctx_ = ctx_.as_ref().clone();
                    ctx_.push(self.meaning(t, ctx));
                    self.meaning(tm.as_ref(), &ctx_)
                } else {
                    panic!()
                }
            }
            Expr::ConsApp(cref, args) => Rc::new(Sem::ConsApp(
                *cref,
                args.iter().map(|arg| self.meaning(arg, ctx)).collect::<Vec<Rc<Sem>>>(),
            )),
            Expr::DeBrujinIdx(idx) => ctx[ctx.len() - 1 - *idx].clone(),
            Expr::DeBrujinLvl(lvl) => ctx[*lvl].clone(),
            Expr::Lam(s) => Rc::new(Sem::Lam(Rc::new(ctx.clone()), s.clone().into())),
            Expr::Match(aref, expr, arms) => {
                if let Sem::ConsApp(cons, args) = self.meaning(expr, ctx).as_ref() {
                    let mut ctx = ctx.clone();

                    for arg in args {
                        ctx.push(arg.clone());
                    }

                    let arm = &arms[cons.1];
                    self.meaning(&arm.1, &ctx)
                } else {
                    Rc::new(Sem::Syn(Box::new(Expr::Match(*aref, expr.clone(), arms.clone()))))
                }
            }
            Expr::Fun(fref) => self.meaning(&self.env.get_function(*fref).0, ctx),
        }
    }

    fn reify(&self, sm: Rc<Sem>) -> Expr {
        match sm.as_ref() {
            Sem::Lam(_, tm) => {
               Expr::Lam(tm.clone())
            },
            Sem::ConsApp(cref, args) => {
                let args = args.iter().map(|arg| self.reify(arg.clone())).collect();

                Expr::ConsApp(*cref, args)
            }
            Sem::Syn(expr) => *expr.clone(),
        }
    }

    pub fn eval(&self, tm: &Expr) -> Expr {
        let mut ctx = Vec::new();
        let mut tm = tm.clone();
        tm.convert_lvl_to_idx(0);

        let val = self.meaning(&tm, &ctx);

        self.reify(val.into())
    }
}
