use std::{borrow::Cow, cell::RefCell, rc::Rc};

use super::{
    env::Env,
    expr::{ConsRef, Expr},
};

#[derive(Debug)]
enum Sem<'a> {
    Lam(&'a RefCell<Cow<'a, Vec<Rc<Sem<'a>>>>>, &'a Expr),
    ConsApp(ConsRef, Vec<Rc<Sem<'a>>>),
    Syn(&'a Expr),
}

pub struct EvalContext<'a> {
    env: &'a Env,
}

impl<'a> EvalContext<'a> {
    pub fn new(env: &'a Env) -> Self {
        Self { env }
    }

    fn meaning(&self, tm: &'a Expr, ctx: &'a RefCell<Cow<'a, Vec<Rc<Sem<'a>>>>>) -> Rc<Sem<'a>> {
        match tm {
            Expr::App(s, t) => {
                let res = self.meaning(s, ctx);
                if let Sem::Lam(ctx_, tm) = res.as_ref() {
                    ctx_.borrow_mut().to_mut().push(self.meaning(t, ctx));
                    self.meaning(tm, ctx_)
                } else {
                    panic!()
                }
            }
            Expr::ConsApp(cref, args) => Rc::new(Sem::ConsApp(
                *cref,
                args.iter()
                    .map(|arg| self.meaning(arg, ctx))
                    .collect::<Vec<Rc<Sem>>>(),
            )),
            Expr::DeBrujinIdx(idx) => {
                let ctx = ctx.borrow();
                ctx[ctx.len() - 1 - *idx].clone()
            }
            Expr::DeBrujinLvl(lvl) => ctx.borrow()[*lvl].clone(),
            Expr::Lam(s) => Rc::new(Sem::<'a>::Lam(ctx, s)),
            Expr::Match(_aref, expr, arms) => {
                if let Sem::ConsApp(cons, args) = self.meaning(expr, ctx).as_ref() {
                    {
                        let mut ctx = ctx.borrow_mut();
                        let ctx = ctx.to_mut();

                        for arg in args {
                            ctx.push(arg.clone());
                        }
                    }

                    let arm = &arms[cons.1];
                    self.meaning(&arm.1, ctx)
                } else {
                    Rc::new(Sem::Syn(&tm))
                }
            }
            Expr::Fun(fref) => self.meaning(&self.env.get_function(*fref).0, ctx),
        }
    }

    fn reify(&self, sm: Rc<Sem>) -> Option<Expr> {
        if let Sem::ConsApp(cref, args) = sm.as_ref() {
            let args = args
                .iter()
                .map(|arg| self.reify(arg.clone()).unwrap())
                .collect();
            Some(Expr::ConsApp(*cref, args))
        } else {
            None
        }
    }

    pub fn eval(&self, tm: &Expr) -> Option<Expr> {
        let ctx = RefCell::new(Cow::Owned(Vec::new()));
        let mut tm = tm.clone();
        tm.convert_lvl_to_idx(0);

        let val = self.meaning(&tm, &ctx);

        self.reify(val.into())
    }
}
