use std::collections::HashMap as Map;

use super::{
    check::{Subst, Types},
    exp::{AdtRef, Env},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Scheme(pub Vec<TypeVar>, pub Box<Type>);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeVar(usize);

impl std::fmt::Display for TypeVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "'{}", self.0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Scheme(Scheme),
    Var(TypeVar),
    Lam(Box<Type>, Box<Type>),
    Adt(AdtRef),
    Prim(PrimType),
}

pub struct TypeEnv<'a>(pub &'a Env, pub &'a Type);

impl std::fmt::Display for TypeEnv<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let TypeEnv(env, ty) = self;

        match ty {
            Type::Scheme(scheme) => {
                if !scheme.0.is_empty() {
                    write!(f, "!")?;

                    for TypeVar(var) in &scheme.0 {
                        write!(f, " '{var}")?;
                    }

                    write!(f, ": ")?;
                }

                TypeEnv(env, &scheme.1).fmt(f)
            }
            Type::Var(TypeVar(var)) => write!(f, "'{var}"),
            Type::Lam(ty1, ty2) => write!(f, "{} → {}", TypeEnv(env, &*ty1), TypeEnv(env, &*ty2)),
            Type::Adt(adt) =>  write!(f, "{}", env.get_adt(*adt).name),
            Type::Prim(_) => todo!(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PrimType {
    Int,
}

#[derive(Debug, Clone, Default)]
pub struct Fresh(usize);

impl Fresh {
    pub fn instantiate(&mut self, scheme: &Scheme) -> Type {
        let mut map = Map::new();

        for var in &scheme.0 {
            let nvar = Type::Var(self.new_type_var());
            map.insert(*var, nvar);
        }

        let mut t = *scheme.1.clone();

        t.apply(&Subst(map));

        t
    }

    pub fn new_type_var(&mut self) -> TypeVar {
        self.0 += 1;

        TypeVar(self.0 - 1)
    }
}
