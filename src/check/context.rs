
pub mod TypeCtxImpl {
    use std::{
        collections::{HashMap as Map, HashSet as Set},
        fmt::Display,
        rc::Rc,
    };
    
    use super::super::{
        check::{Subst, Types},
        r#type::{Scheme, Type, TypeVar},
    };
    

    #[derive(Debug, Clone, Default)]
    pub struct TypeCtx {
        env: Map<Rc<str>, Scheme>,
        undo_stack: Vec<UndoAction>,
    }

    #[derive(Debug, Clone)]
    pub enum UndoAction {
        Insert(Rc<str>, Scheme),
        Remove(Rc<str>),
    }

    #[derive(Debug, Clone, Copy)]
    pub struct Savepoint(usize);

    impl TypeCtx {
        pub fn get(&self, name: &str) -> Option<&Scheme> {
            self.env.get(name)
        }

        pub fn generalize(&self, ty: &Type) -> Scheme {
            let mut vars = ty.ftv();

            for name in &self.ftv() {
                vars.remove(name);
            }

            Scheme(vars.into_iter().collect(), Box::new(ty.clone()))
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

        pub fn restore(&mut self, savepoint: Savepoint) {
            while self.undo_stack.len() > savepoint.0 {
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

        pub fn savepoint(&self) -> Savepoint {
            Savepoint(self.undo_stack.len())
        }
    }

    impl Display for TypeCtx {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            let mut iter = self.env.iter();

            if let Some((key, value)) = iter.next() {
                write!(f, "{key}: {value:#?}")?;
                for (key, value) in iter {
                    write!(f, ", {key}: {value:#?}")?;
                }
            }

            Ok(())
        }
    }

    impl Types for TypeCtx {
        fn ftv(&self) -> Set<TypeVar> {
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
}

pub use TypeCtxImpl::TypeCtx;

pub mod LetBindingsImpl {
    use std::{collections::HashMap as Map, rc::Rc};

    use crate::check::exp::Expr;


    #[derive(Debug, Clone, Default)]
    pub struct LetBindings {
        map: Map<Rc<str>, Box<Expr>>,

        undo_stack: Vec<UndoAction>
    }

    impl LetBindings {
        pub fn push(&mut self, name: Rc<str>, expr: Box<Expr>) -> Savepoint {
            let savepoint = self.undo_stack.len();

            match self.map.insert(name.clone(), expr) {
                Some(expr) => {
                    self.undo_stack.push(UndoAction::Insert(name, expr));
                },
                None => {
                    self.undo_stack.push(UndoAction::Remove(name));
                },
            }

            Savepoint(savepoint)
        }

        pub fn restore(&mut self, savepoint: Savepoint) {
            while self.undo_stack.len() > savepoint.0 {
                if let Some(action) = self.undo_stack.pop() {
                    match action {
                        UndoAction::Remove(name) => { self.map.remove(&name); },
                        UndoAction::Insert(name, expr) => { self.map.insert(name, expr); },
                    }
                }
            }
        }

        pub fn get(&self, name: &str, level: usize) -> Option<Box<Expr>> {
            if let Some(expr) = self.map.get(name) {
                Some(expr.clone())
            } else {
                None
            }
        }
    }

    pub struct Savepoint(usize);

    #[derive(Debug, Clone)]
    enum UndoAction {
        Remove(Rc<str>),
        Insert(Rc<str>, Box<Expr>)
    }
}

pub use LetBindingsImpl::LetBindings;