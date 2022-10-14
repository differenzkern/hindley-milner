use std::collections::{HashMap as Map, HashSet as Set};
use std::rc::Rc;

use super::check::{Subst, Types};
use super::expr::Expr;
use super::r#type::{Scheme, Type, TypeVar};

#[derive(Clone, Copy)]
pub struct Savepoint(usize);

#[derive(Debug, Default)]
pub struct Ctx {
    pub(crate) types: Map<Rc<str>, Scheme<Type>>,

    locals: Map<Rc<str>, Local>,

    level: usize,

    undo_stack: Vec<UndoAction>,
}

#[derive(Debug)]
enum UndoAction {
    ReplaceLocal(Rc<str>, Local, bool),
    ReplaceType(Rc<str>, Scheme<Type>),
    InsertLocal(Rc<str>, bool),
    RemoveType(Rc<str>, Scheme<Type>),
    InsertType(Rc<str>),
}

#[derive(Debug, Clone)]
enum Local {
    DeBrujinLvl(usize),
    Expr(Rc<Expr>),
}

impl Ctx {
    pub fn generalize(&self, ty: &Type) -> Scheme<Type> {
        let mut vars = ty.ftv();

        for name in &self.ftv() {
            vars.remove(name);
        }

        Scheme(Some(vars.into_iter().collect()), ty.clone())
    }

    pub fn insert_ty(&mut self, name: Rc<str>, scheme: Scheme<Type>) {
        if let Some(scheme) = self.types.insert(name.clone(), scheme) {
            self.undo_stack.push(UndoAction::ReplaceType(name, scheme));
        } else {
            self.undo_stack.push(UndoAction::InsertType(name));
        }
    }

    pub fn push_local(&mut self, name: Rc<str>, ty: Type) {
        if let Some(expr) = self
            .locals
            .insert(name.clone(), Local::DeBrujinLvl(self.level))
        {
            self.undo_stack
                .push(UndoAction::ReplaceLocal(name.clone(), expr, true));

            if let Some(scheme) = self.types.insert(name.clone(), Scheme(None, ty)) {
                self.undo_stack.push(UndoAction::ReplaceType(name, scheme));
            } else {
                self.undo_stack.push(UndoAction::InsertType(name));
            }
        } else {
            self.undo_stack
                .push(UndoAction::InsertLocal(name.clone(), true));

            if let Some(scheme) = self.types.insert(name.clone(), Scheme(None, ty)) {
                self.undo_stack.push(UndoAction::ReplaceType(name, scheme));
            } else {
                self.undo_stack.push(UndoAction::InsertType(name));
            }
        }

        self.level += 1;
    }

    pub fn push_let(&mut self, name: Rc<str>, expr: Rc<Expr>, scheme: Scheme<Type>) {
        if let Some(expr) = self.locals.insert(name.clone(), Local::Expr(expr)) {
            self.undo_stack
                .push(UndoAction::ReplaceLocal(name.clone(), expr, false));

            if let Some(scheme) = self.types.remove(&name) {
                self.undo_stack.push(UndoAction::ReplaceType(name, scheme));
            } else {
                self.undo_stack.push(UndoAction::InsertType(name));
            }
        } else {
            self.undo_stack
                .push(UndoAction::InsertLocal(name.clone(), false));

            if let Some(scheme) = self.types.insert(name.clone(), scheme) {
                self.undo_stack.push(UndoAction::ReplaceType(name, scheme));
            } else {
                self.undo_stack.push(UndoAction::InsertType(name));
            }
        }
    }

    pub fn restore(&mut self, savepoint: Savepoint) {
        while self.undo_stack.len() > savepoint.0 {
            let dec = match self.undo_stack.pop().unwrap() {
                UndoAction::ReplaceLocal(name, expr, dec_level) => {
                    self.locals.insert(name.clone(), expr).unwrap();
                    dec_level
                }
                UndoAction::InsertLocal(name, dec_level) => {
                    self.locals.remove(&name);
                    dec_level
                }
                UndoAction::ReplaceType(name, scheme) => {
                    self.types.insert(name, scheme);
                    false
                }
                UndoAction::RemoveType(name, scheme) => {
                    self.types.insert(name, scheme);
                    false
                }
                UndoAction::InsertType(name) => {
                    self.types.remove(&name);
                    false
                }
            };

            if dec {
                self.level -= 1;
            }
        }
    }

    pub fn hide(&mut self, name: &Rc<str>) {
        if let Some(scheme) = self.types.remove(name) {
            self.undo_stack
                .push(UndoAction::RemoveType(name.clone(), scheme));
        }
    }

    pub fn get(&self, name: &Rc<str>, lvl: usize) -> Option<(Option<Rc<Expr>>, &Scheme<Type>)> {
        self.types.get(name).map(|scheme| {
            (
                self.locals.get(name).map(|local| match local {
                    Local::DeBrujinLvl(lvl_) => Rc::new(Expr::DeBrujinIdx(lvl - 1 - lvl_)),
                    Local::Expr(expr) => expr.clone(),
                }),
                scheme,
            )
        })
    }

    pub fn save(&self) -> Savepoint {
        Savepoint(self.undo_stack.len())
    }

    pub fn level(&self) -> usize {
        self.level
    }
}

impl Types for Ctx {
    fn ftv(&self) -> Set<TypeVar> {
        self.types
            .values()
            .cloned()
            .collect::<Vec<Scheme<Type>>>()
            .ftv()
    }

    fn apply(&mut self, s: &Subst) {
        for value in self.types.values_mut() {
            value.apply(s);
        }

        for action in self.undo_stack.iter_mut() {
            match action {
                UndoAction::ReplaceType(_, scheme) | UndoAction::RemoveType(_, scheme) => {
                    scheme.apply(s)
                }
                _ => {}
            }
        }
    }
}
