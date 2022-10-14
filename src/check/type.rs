use std::collections::HashMap as Map;

use super::{
    check::{Subst, Types},
    env::Env,
    expr::AdtRef,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Scheme<T: Types>(pub Option<Vec<TypeVar>>, pub T);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeVar(usize);

impl std::fmt::Display for TypeVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "'{}", self.0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Var(TypeVar),
    Lam(Box<Type>, Box<Type>),
    Adt(AdtRef),
    Prim(PrimType),
}

pub struct TypePrinter<'a>(pub &'a Env, pub &'a Type);

impl std::fmt::Display for TypePrinter<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let TypePrinter(env, ty) = self;

        match ty {
            /*Type::Scheme(scheme) => {
                if !scheme.0.is_empty() {
                    write!(f, "!")?;

                    for TypeVar(var) in &scheme.0 {
                        write!(f, " '{var}")?;
                    }

                    write!(f, ": ")?;
                }

                TypePrinter(env, &scheme.1).fmt(f)
            }*/
            Type::Var(TypeVar(var)) => write!(f, "'{var}"),
            Type::Lam(ty1, ty2) => write!(
                f,
                "{} → {}",
                TypePrinter(env, &*ty1),
                TypePrinter(env, &*ty2)
            ),
            Type::Adt(adt) => write!(f, "{}", env.get_adt(*adt).0),
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
    pub fn instantiate(&mut self, scheme: &Scheme<Type>) -> Type {
        let mut map = Map::new();

        if let Some(vars) = &scheme.0 {
            for var in vars {
                let nvar = Type::Var(self.new_type_var());
                map.insert(*var, nvar);
            }
        }
        

        let mut t = scheme.1.clone();

        t.apply(&Subst(map));

        t
    }

    pub fn new_type_var(&mut self) -> TypeVar {
        self.0 += 1;

        TypeVar(self.0 - 1)
    }
}
