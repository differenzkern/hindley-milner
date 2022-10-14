use std::rc::Rc;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FunRef(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
    App(Rc<Expr>, Rc<Expr>),
    ConsApp(ConsRef, Vec<Rc<Expr>>),
    DeBrujinIdx(usize),
    Lam(Rc<Expr>),
    Match(AdtRef, Rc<Expr>, Vec<(usize, Rc<Expr>)>),
    Fun(FunRef),
}

impl Expr {
    /*
    pub fn convert_lvl_to_idx(&mut self, level: usize) {
        match self {
            Expr::App(e1, e2) => {
                e1.convert_lvl_to_idx(level);
                e2.convert_lvl_to_idx(level);
            }
            Expr::ConsApp(_, e2) => {
                e2.iter_mut().for_each(|e| e.convert_lvl_to_idx(level));
            }
            /*Expr::DeBrujinLvl(lvl) => {
                *self = Expr::DeBrujinIdx(level - 1 - *lvl);
            }*/
            Expr::Lam(expr) => expr.convert_lvl_to_idx(level + 1),
            Expr::Match(_, e1, e2) => {
                e1.convert_lvl_to_idx(level);
                e2.iter_mut()
                    .for_each(|(args, e)| e.convert_lvl_to_idx(level + *args));
            }
            _ => {}
        }
    }*/
    /*

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
    }*/
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
