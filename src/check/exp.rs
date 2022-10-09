use std::collections::HashMap as Map;
use std::rc::Rc;

use crate::parse::ast::{AdtDef, Constructor};

use super::r#type::Type;

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
pub struct FunRef(usize);

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

#[derive(Debug, Clone, Default)]
pub struct Env {
    pub types: Vec<AdtDef>,
    pub functions: Vec<(Expr, Type)>,

    pub adts: Vec<Vec<Cons>>,

    pub adt_map: Map<Rc<str>, AdtRef>,
    pub fun_map: Map<Rc<str>, FunRef>,
    pub con_map: Map<Rc<str>, ConsRef>,
    pub curried_con_map: Map<Rc<str>, Box<Expr>>,
}

impl Env {
    pub fn get_function(&self, fref: FunRef) -> &(Expr, Type) {
        self.functions.get(fref.0).unwrap()
    }

    pub fn get_cons(&self, cref: ConsRef) -> &Constructor {
        self.types
            .get(cref.0 .0)
            .unwrap()
            .constructors
            .get(cref.1)
            .unwrap()
    }

    pub fn get_adt(&self, adt_ref: AdtRef) -> &AdtDef {
        self.types.get(adt_ref.0).unwrap()
    }

    pub fn lookup_cons<'a>(&self, name: &'a str) -> Result<ConsRef, EnvError<'a>> {
        match self.con_map.get(name) {
            Some(value) => Ok(*value),
            None => Err(EnvError::SymbolNotFound(name)),
        }
    }

    pub fn lookup_curried_cons<'a>(&self, name: &'a str) -> Result<Box<Expr>, EnvError<'a>> {
        match self.curried_con_map.get(name) {
            Some(value) => Ok(Box::clone(value)),
            None => Err(EnvError::SymbolNotFound(name)),
        }
    }

    pub fn lookup_adt<'a>(&self, name: &'a str) -> Result<AdtRef, EnvError<'a>> {
        match self.adt_map.get(name) {
            Some(value) => Ok(*value),
            None => Err(EnvError::SymbolNotFound(name)),
        }
    }

    pub fn lookup_fun<'a>(&self, name: &'a str) -> Result<FunRef, EnvError<'a>> {
        match self.fun_map.get(name) {
            Some(value) => Ok(*value),
            None => Err(EnvError::SymbolNotFound(name)),
        }
    }

    pub fn insert_function(
        &mut self,
        name: Rc<str>,
        expr: Expr,
        r#type: Type,
    ) -> Result<FunRef, ()> {
        if let std::collections::hash_map::Entry::Vacant(e) = self.fun_map.entry(name) {
            let idx = self.functions.len();
            self.functions.push((expr, r#type));
            e.insert(FunRef(idx));

            Ok(FunRef(idx))
        } else {
            Err(())
        }
    }

    pub fn deref_cons(&self, cref: ConsRef) -> &Cons {
        &self.adts[cref.0 .0][cref.1]
    }

    pub fn insert_adt(&mut self, def: AdtDef) -> Result<AdtRef, ()> {
        if self.adt_map.contains_key(&def.name) {
            return Err(());
        }

        for cons in &def.constructors {
            if self.con_map.contains_key(&cons.name) {
                return Err(());
            }
        }

        let adt_ref = AdtRef(self.types.len());
        self.adt_map.insert(def.name.clone(), adt_ref);

        for (idx, con) in def.constructors.iter().enumerate() {
            let mut r#type = Type::Adt(adt_ref);
            let mut expr = Expr::ConsApp(
                ConsRef(adt_ref, idx),
                (0usize..con.arguments.len())
                    .rev()
                    .map(|idx| Expr::DeBrujinIdx(idx as i64))
                    .collect(),
            );

            for arg in con.arguments.iter().rev() {
                if arg.as_ref() == def.name.as_ref() {
                    r#type = Type::Lam(Box::new(Type::Adt(adt_ref)), Box::new(r#type));
                } else {
                    r#type = Type::Lam(
                        Box::new(Type::Adt(self.lookup_adt(arg.as_ref()).unwrap())),
                        Box::new(r#type),
                    );
                }
                expr = Expr::Lam(Box::new(expr));
            }

            self.con_map.insert(con.name.clone(), ConsRef(adt_ref, idx));
            self.curried_con_map
                .insert(con.name.clone(), Box::new(expr));
        }

        self.types.push(def);

        Ok(adt_ref)
    }

    pub fn is_fresh(&self, name: &str) -> bool {
        !self.fun_map.contains_key(name) && !self.adt_map.contains_key(name)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    App(Box<Expr>, Box<Expr>),
    ConsApp(ConsRef, Vec<Expr>),
    DeBrujinIdx(i64),
    DeBrujinLvl(i64),
    Lam(Box<Expr>),
    Match(Box<Expr>, Vec<Expr>),
    Fun(FunRef),
}

impl Expr {
    /*pub fn convert_lvl_to_idx(&mut self, level: i64) {
        match self {
            Expr::App(e1, e2) => { e1.convert_lvl_to_idx(level); e2.convert_lvl_to_idx(level); },
            Expr::ConsApp(e1, e2) => { e2.into_iter().map(|e| e.convert_lvl_to_idx(level)); },
            Expr::DeBrujinLvl(level_) => { *self = Expr::DeBrujinIdx(level - 1 - *level_); },
            Expr::Lam(e) => { e.convert_lvl_to_idx(level); },
            Expr::Match(e1, e2) => {e1.convert_lvl_to_idx(level); e2.iter_mut().for_each(|e| e.convert_lvl_to_idx(level)); },
            _ => {}
        }
    }*/

    pub fn convert_idx_to_lvl(&mut self, level: i64, max_idx: i64) {
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
            Expr::Match(e1, e2) => {
                e1.convert_idx_to_lvl(level, max_idx);
                e2.iter_mut()
                    .for_each(|e| e.convert_idx_to_lvl(level, max_idx));
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
