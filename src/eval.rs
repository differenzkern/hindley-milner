use crate::{type_env::TypeEnv, check::Fresh, Type};

use crate::parse::ast::Expr as Term;

enum Sem {
    
}

struct Env {

}

struct EvalState {
    fresh: Fresh,
    context: TypeEnv,
}

impl EvalState {
    /// ↑ᵀ: map neutral terms of type T to semantic objects in〚T〛
    fn reflect(ty: Type, tm: Term) -> Sem {
        todo!()
    }

    /// ↓ᵀ: maps semantic objects in 〚T〛to normal forms of type T
    fn reify(ty: Type, v: Sem) -> Term {
        match ty {
            Type::Algebraic(adt) => todo!(),
            Type::Var(_) => todo!(),
            Type::Int => todo!(),
            Type::Fun(_, _) => todo!(),
        }
    }

}