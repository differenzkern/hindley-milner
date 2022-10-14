use std::collections::HashMap as Map;
use std::rc::Rc;

use crate::syntax::ast::{AdtDef, Constructor};

use super::{
    expr::{AdtRef, Cons, ConsRef, EnvError, Expr, FunRef},
    r#type::{Scheme, Type},
};

#[derive(Debug, Clone, Default)]
pub struct Env {
    funs: Vec<(Rc<str>, Rc<Expr>, Scheme<Type>)>,
    adts: Vec<(Rc<str>, Vec<(Rc<str>, Cons)>)>,

    types: Map<Rc<str>, AdtRef>,
    exprs: Map<Rc<str>, (DefType, Rc<Expr>, Scheme<Type>)>,
}

#[derive(Debug, Clone)]
pub enum DefType {
    Cons(ConsRef),
    Fun(FunRef),
}

impl Env {
    pub fn lookup(&self, name: &str) -> Option<&(DefType, Rc<Expr>, Scheme<Type>)> {
        self.exprs.get(name)
    }

    pub fn lookup_adt(&self, name: &str) -> Result<AdtRef, &'static str> {
        self.types
            .get(name)
            .ok_or("algebraic data type not found")
            .copied()
    }

    pub fn lookup_cons(&self, name: &str) -> Result<ConsRef, &'static str> {
        match self.exprs.get(name) {
            Some((def, _, _)) => match def {
                DefType::Cons(cons) => Ok(*cons),
                DefType::Fun(_) => Err("expected constructor found function"),
            },
            None => Err("symbol not found"),
        }
    }

    pub fn get_adt(&self, aref: AdtRef) -> &(Rc<str>, Vec<(Rc<str>, Cons)>) {
        &self.adts[aref.0]
    }

    pub fn get_cons(&self, cref: ConsRef) -> &(Rc<str>, Cons) {
        &self.adts[cref.0 .0].1[cref.1]
    }

    pub fn get_fun(&self, fref: FunRef) -> &(Rc<str>, Rc<Expr>, Scheme<Type>) {
        &self.funs[fref.0]
    }

    pub fn insert_fun(&mut self, name: Rc<str>, expr: Rc<Expr>, r#type: Scheme<Type>) -> FunRef {
        let fun_ref = FunRef(self.funs.len());
        self.funs.push((name.clone(), expr.clone(), r#type.clone()));
        assert!(self
            .exprs
            .insert(name, (DefType::Fun(fun_ref), expr, r#type))
            .is_none());

        fun_ref
    }

    pub fn insert_adt(&mut self, def: AdtDef) -> AdtRef {
        let adt_ref = AdtRef(self.adts.len());
        let mut cons = Vec::new();

        for (idx, cons_) in def.constructors.into_iter().enumerate() {
            let cons_ref = ConsRef(adt_ref, idx);
            let mut expr = Rc::new(Expr::ConsApp(
                ConsRef(adt_ref, idx),
                (0..cons_.arguments.len())
                    .map(|idx| Rc::new(Expr::DeBrujinIdx(idx)))
                    .collect(),
            ));
            let mut r#type = Type::Adt(adt_ref);

            for name in cons_.arguments.iter().rev() {
                expr = Rc::new(Expr::Lam(expr));
                r#type = if name != &def.name {
                    Type::Lam(
                        Box::new(Type::Adt(self.lookup_adt(name).unwrap())),
                        Box::new(r#type),
                    )
                } else {
                    Type::Lam(Box::new(Type::Adt(adt_ref)), Box::new(r#type))
                }
            }

            let mut cons_args = Vec::new();
            for name in &cons_.arguments {
                if name != &def.name {
                    cons_args.push(self.lookup_adt(name).unwrap());
                } else {
                    cons_args.push(adt_ref);
                }
            }

            cons.push((cons_.name.clone(), Cons(cons_ref, cons_args)));

            assert!(self
                .exprs
                .insert(
                    cons_.name,
                    (DefType::Cons(cons_ref), expr, Scheme(None, r#type))
                )
                .is_none());
        }

        self.adts.push((def.name.clone(), cons));
        self.types.insert(def.name, adt_ref);

        adt_ref
    }

    pub fn is_fresh(&self, name: &str) -> bool {
        !self.exprs.contains_key(name) && !self.types.contains_key(name)
    }

    pub fn next_fun(&self) -> FunRef {
        FunRef(self.funs.len())
    }

    pub fn get_cons_name(&self, cref: ConsRef) -> &Rc<str> {
        &self.get_cons(cref).0
    }

    pub fn get_fun_name(&self, fref: FunRef) -> &Rc<str> {
        &self.get_fun(fref).0
    }

    pub fn get_adt_name(&self, aref: AdtRef) -> &Rc<str> {
        &self.get_adt(aref).0
    }

    fn pretty_print(
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
                write!(f, "{} ", self.get_cons_name(*cref))?;
                for expr in args {
                    self.pretty_print(expr, lvl, f)?;
                }
                Ok(())
            }
            Expr::DeBrujinIdx(idx) => write!(f, "{} ", lvl - 1 - *idx),
            Expr::Lam(expr) => {
                write!(f, "λ {lvl}. ")?;
                self.pretty_print(expr, lvl + 1, f)
            }
            Expr::Match(aref, expr, arms) => {
                write!(f, "match ")?;
                self.pretty_print(expr, lvl, f)?;
                write!(f, "{{ ")?;
                for (idx, (cons_args_num, expr)) in arms.iter().enumerate() {
                    write!(f, "| {}", self.get_cons_name(ConsRef(*aref, idx)))?;
                    for arg in lvl..lvl + cons_args_num {
                        write!(f, " {arg}")?;
                    }
                    write!(f, " → ")?;
                    self.pretty_print(expr, lvl + cons_args_num, f)?;
                }

                write!(f, "}} ")
            }
            Expr::Fun(fref) => {
                write!(f, "{} ", self.get_fun_name(*fref))
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
