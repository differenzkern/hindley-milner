use std::collections::HashMap as Map;
use std::rc::Rc;

use crate::syntax::ast::{AdtDef, Constructor};

use super::{
    expr::{AdtRef, Cons, ConsRef, EnvError, Expr, FunRef},
    r#type::Type,
};

#[derive(Debug, Clone, Default)]
pub struct Env {
    pub types: Vec<AdtDef>,
    pub functions: Vec<(Expr, Type, Rc<str>)>,

    pub adts: Vec<Vec<Cons>>,

    pub adt_map: Map<Rc<str>, AdtRef>,
    pub fun_map: Map<Rc<str>, FunRef>,
    pub con_map: Map<Rc<str>, ConsRef>,
    pub curried_con_map: Map<Rc<str>, Box<Expr>>,
}

impl Env {
    pub fn get_function(&self, fref: FunRef) -> &(Expr, Type, Rc<str>) {
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

    pub fn lookup(&self, name: &str) -> Option<Expr> {
        self.lookup_fun(name)
            .to_owned()
            .map(Expr::Fun)
            .or_else(|_| self.lookup_curried_cons(name).map(|expr| *expr))
            .ok()
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
        if let std::collections::hash_map::Entry::Vacant(e) = self.fun_map.entry(name.clone()) {
            let idx = self.functions.len();
            self.functions.push((expr, r#type, name));
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
                    .map(|idx| Expr::DeBrujinIdx(idx))
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

    pub fn pretty_print(
        &self,
        expr: &Expr,
        lvl: usize,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        match expr {
            Expr::App(e1, e2) => {
                write!(f, "(")?;
                self.pretty_print(e1, lvl, f)?;
                write!(f, ") (")?;
                self.pretty_print(e2, lvl, f)?;
                write!(f, ")")
            }
            Expr::ConsApp(cref, args) => {
                let cons = self.get_cons(*cref);
                write!(f, "{} ", cons.name)?;
                for (expr, _ty) in args.iter().zip(
                    cons.arguments
                        .iter()
                        .map(|arg| Type::Adt(self.lookup_adt(arg).unwrap())),
                ) {
                    self.pretty_print(expr, lvl, f)?;
                }
                Ok(())
            }
            Expr::DeBrujinIdx(idx) => write!(f, "{} ", lvl - 1 - *idx),
            Expr::DeBrujinLvl(lvl) => write!(f, "{lvl} "),
            Expr::Lam(expr) => {
                write!(f, "λ {lvl}. ")?;
                self.pretty_print(expr, lvl + 1, f)
            }
            Expr::Match(aref, expr, arms) => {
                write!(f, "match ")?;
                self.pretty_print(expr, lvl, f)?;
                write!(f, "{{ ")?;
                for (idx, arm) in arms.iter().enumerate() {
                    let cons = self.get_cons(ConsRef(*aref, idx));
                    write!(f, "| {}", cons.name)?;
                    for args in &cons.arguments {
                        write!(f, " {args}")?;
                    }
                    write!(f, " → ")?;
                    self.pretty_print(&arm.1, lvl + cons.arguments.len(), f)?;
                }

                write!(f, "}} ")
            }
            Expr::Fun(fref) => {
                write!(f, "{} ", self.get_function(*fref).2)
            }
            _ => panic!(),
        }
    }
}

pub struct ExprPrinter<'a>(pub &'a Env, pub &'a Expr, pub usize);

impl std::fmt::Display for ExprPrinter<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.pretty_print(self.1, self.2, f)
    }
}
