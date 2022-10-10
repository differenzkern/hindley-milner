use std::collections::{HashMap as Map, HashSet as Set};
use std::rc::Rc;

use super::check::{Subst, Types};
use super::expr::Expr;
use super::r#type::{Scheme, Type, TypeVar};

#[derive(Clone, Copy)]
pub struct Savepoint(usize);

#[derive(Debug, Default)]
pub struct Ctx {
    types: Map<Rc<str>, Scheme>,

    locals: Map<Rc<str>, Expr>,

    level: usize,

    undo_stack: Vec<UndoAction>,
}

#[derive(Debug)]
enum UndoAction {
    ReplaceLocal(Rc<str>, Expr, bool),
    ReplaceType(Rc<str>, Scheme),
    InsertLocal(Rc<str>, bool),
    RemoveType(Rc<str>, Scheme),
    InsertType(Rc<str>),
}

impl Ctx {
    pub fn generalize(&self, ty: &Type) -> Scheme {
        let mut vars = ty.ftv();

        for name in &self.ftv() {
            vars.remove(name);
        }

        Scheme(vars.into_iter().collect(), Box::new(ty.clone()))
    }

    pub fn insert_ty(&mut self, name: Rc<str>, scheme: Scheme) {
        if let Some(scheme) = self.types.insert(name.clone(), scheme) {
            self.undo_stack.push(UndoAction::ReplaceType(name, scheme));
        } else {
            self.undo_stack.push(UndoAction::InsertType(name));
        }
    }

    pub fn push_local(&mut self, name: Rc<str>, ty: Box<Type>) {
        if let Some(expr) = self
            .locals
            .insert(name.clone(), Expr::DeBrujinLvl(self.level))
        {
            self.undo_stack
                .push(UndoAction::ReplaceLocal(name.clone(), expr, true));

            if let Some(scheme) = self.types.insert(name.clone(), Scheme(vec![], ty)) {
                self.undo_stack.push(UndoAction::ReplaceType(name, scheme));
            } else {
                self.undo_stack.push(UndoAction::InsertType(name));
            }
        } else {
            self.undo_stack
                .push(UndoAction::InsertLocal(name.clone(), true));

            if let Some(scheme) = self.types.insert(name.clone(), Scheme(vec![], ty)) {
                self.undo_stack.push(UndoAction::ReplaceType(name, scheme));
            } else {
                self.undo_stack.push(UndoAction::InsertType(name));
            }
        }

        self.level += 1;
    }

    pub fn push_let(&mut self, name: Rc<str>, expr: Expr, scheme: Scheme) {
        if let Some(expr) = self.locals.insert(name.clone(), expr) {
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

    pub fn get(&self, name: &Rc<str>) -> Option<(Option<&Expr>, &Scheme)> {
        self.types
            .get(name)
            .map(|scheme| (self.locals.get(name), scheme))
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
        self.types.values().cloned().collect::<Vec<Scheme>>().ftv()
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
