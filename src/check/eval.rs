use std::rc::Rc;

use super::{
    env::Env,
    expr::{ConsRef, Expr},
};

#[derive(Debug)]
enum Sem {
    Lam(Rc<Vec<Rc<Sem>>>, Rc<Expr>),
    ConsApp(ConsRef, Vec<Rc<Sem>>),
    Syn(Rc<Expr>),
}

pub struct EvalContext<'a> {
    env: &'a Env,
}

impl<'a> EvalContext<'a> {
    pub fn new(env: &'a Env) -> Self {
        Self { env }
    }

    fn meaning(&self, tm: &Expr, ctx: &Vec<Rc<Sem>>) -> Rc<Sem> {
        match tm {
            Expr::App(s, t) => {
                if let Sem::Lam(ctx_, tm) = self.meaning(s, ctx).as_ref() {
                    let mut ctx_ = ctx_.as_ref().clone();
                    ctx_.push(self.meaning(t, ctx));
                    self.meaning(tm.as_ref(), &ctx_)
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
            Expr::DeBrujinIdx(idx) => ctx[ctx.len() - 1 - *idx].clone(),
            Expr::Lam(s) => Rc::new(Sem::Lam(Rc::new(ctx.clone()), s.clone())),
            Expr::Match(aref, expr, arms) => {
                if let Sem::ConsApp(cons, args) = self.meaning(expr, ctx).as_ref() {
                    let mut ctx = ctx.clone();

                    for arg in args {
                        ctx.push(arg.clone());
                    }

                    let arm = &arms[cons.1];
                    self.meaning(&arm.1, &ctx)
                } else {
                    Rc::new(Sem::Syn(Rc::new(Expr::Match(
                        *aref,
                        expr.clone(),
                        arms.clone(),
                    ))))
                }
            }
            Expr::Fun(fref) => self.meaning(self.env.get_fun(*fref).1.as_ref(), ctx),
        }
    }

    fn reify(&self, sm: Rc<Sem>) -> Rc<Expr> {
        match sm.as_ref() {
            Sem::Lam(_, tm) => Rc::new(Expr::Lam(tm.clone())),
            Sem::ConsApp(cref, args) => {
                let args = args.iter().map(|arg| self.reify(arg.clone())).collect();

                Rc::new(Expr::ConsApp(*cref, args))
            }
            Sem::Syn(expr) => expr.clone(),
        }
    }

    pub fn eval(&self, tm: &Expr) -> Option<Rc<Expr>> {
        let mut ctx = Vec::new();
        let mut tm = tm.clone();

        let val = self.meaning(&tm, &ctx);

        let res = self.reify(val.into());

        match res.as_ref() {
            Expr::ConsApp(_, _) => {}
            _ => return None,
        }

        Some(res)
    }
}
