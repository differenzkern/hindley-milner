use std::{borrow::Cow, cell::RefCell, rc::Rc};

use super::env::Env;

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
enum Sem<'a> {
    Lam(&'a RefCell<Cow<'a, Vec<Rc<Sem<'a>>>>>, &'a Expr),
    ConsApp(ConsRef, Vec<Rc<Sem<'a>>>),
    Syn(&'a Expr),
}

pub struct EvalContext<'a> {
    env: &'a Env,
}

impl<'a> EvalContext<'a> {
    pub fn new(env: &'a Env) -> Self {
        Self { env }
    }

    fn meaning(&self, tm: &'a Expr, ctx: &'a RefCell<Cow<'a, Vec<Rc<Sem<'a>>>>>) -> Rc<Sem<'a>> {
        match tm {
            Expr::App(s, t) => {
                let res = self.meaning(s, ctx);
                if let Sem::Lam(ctx_, tm) = res.as_ref() {
                    ctx_.borrow_mut().to_mut().push(self.meaning(t, ctx));
                    self.meaning(tm, ctx_)
                } else {
                    panic!()
                }
            }
            Expr::ConsApp(cref, args) => Rc::new(Sem::ConsApp(
                *cref,
                args.iter()
                    .map(|arg| self.meaning(arg, ctx))
                    .collect::<Vec<Rc<Sem>>>(),
            )),
            Expr::DeBrujinIdx(idx) => {
                let ctx = ctx.borrow();
                ctx[ctx.len() - 1 - *idx].clone()
            }
            Expr::DeBrujinLvl(lvl) => ctx.borrow()[*lvl].clone(),
            Expr::Lam(s) => Rc::new(Sem::<'a>::Lam(ctx, s)),
            Expr::Match(_aref, expr, arms) => {
                if let Sem::ConsApp(cons, args) = self.meaning(expr, ctx).as_ref() {
                    {
                        let mut ctx = ctx.borrow_mut();
                        let ctx = ctx.to_mut();

                        for arg in args {
                            ctx.push(arg.clone());
                        }
                    }

                    let arm = &arms[cons.1];
                    self.meaning(&arm.1, ctx)
                } else {
                    Rc::new(Sem::Syn(&tm))
                }
            }
            Expr::Fun(fref) => self.meaning(&self.env.get_function(*fref).0, ctx),
        }
    }

    fn reify(&self, sm: Rc<Sem>) -> Option<Expr> {
        if let Sem::ConsApp(cref, args) = sm.as_ref() {
            let args = args
                .iter()
                .map(|arg| self.reify(arg.clone()).unwrap())
                .collect();
            Some(Expr::ConsApp(*cref, args))
        } else {
            None
        }
    }

    pub fn eval(&self, tm: &Expr) -> Option<Expr> {
        let ctx = RefCell::new(Cow::Owned(Vec::new()));
        let mut tm = tm.clone();
        tm.convert_lvl_to_idx(0);

        let val = self.meaning(&tm, &ctx);

        self.reify(val.into())
    }
}
