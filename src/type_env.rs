use std::{
    collections::{HashMap as Map, HashSet as Set},
    fmt::Display,
    rc::Rc,
};

use crate::{
    check::{Scheme, Subst, Types},
    Type,
};

#[derive(Debug, Clone, Default)]
pub struct TypeEnv {
    env: Map<Rc<str>, Scheme>,
    undo_stack: Vec<UndoAction>,
}

#[derive(Debug, Clone)]
pub enum UndoAction {
    Insert(Rc<str>, Scheme),
    Remove(Rc<str>),
}

impl TypeEnv {
    pub fn get(&self, name: &str) -> Option<&Scheme> {
        self.env.get(name)
    }

    pub fn generalize(&self, ty: &Type) -> Scheme {
        let mut vars = ty.ftv();

        for name in &self.ftv() {
            vars.remove(name);
        }

        Scheme(vars.into_iter().collect(), ty.clone())
    }

    pub fn remove(&mut self, name: &str) {
        if let Some((name, scheme)) = self.env.remove_entry(name) {
            self.undo_stack.push(UndoAction::Insert(name, scheme));
        }
    }

    pub fn insert(&mut self, name: Rc<str>, scheme: Scheme) {
        if let Some(scheme) = self.env.insert(name.clone(), scheme) {
            self.undo_stack.push(UndoAction::Insert(name, scheme));
        } else {
            self.undo_stack.push(UndoAction::Remove(name));
        }
    }

    pub fn undo(&mut self, pos: usize) {
        while self.undo_stack.len() > pos {
            match self.undo_stack.pop().unwrap() {
                UndoAction::Insert(name, scheme) => {
                    self.env.insert(name, scheme);
                }
                UndoAction::Remove(name) => {
                    self.env.remove(&name);
                }
            }
        }
    }

    pub fn savepoint(&self) -> usize {
        self.undo_stack.len()
    }
}

impl Display for TypeEnv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut iter = self.env.iter();

        if let Some((key, value)) = iter.next() {
            write!(f, "{key}: {value}")?;
            for (key, value) in iter {
                write!(f, ", {key}: {value}")?;
            }
        }

        Ok(())
    }
}

impl Types for TypeEnv {
    fn ftv(&self) -> Set<usize> {
        self.env.values().cloned().collect::<Vec<Scheme>>().ftv()
    }

    fn apply(&mut self, s: &Subst) {
        for value in self.env.values_mut() {
            value.apply(s);
        }

        for action in self.undo_stack.iter_mut() {
            if let UndoAction::Insert(_, scheme) = action {
                scheme.apply(s);
            }
        }
    }
}
