use crate::Expr;

fn substitute(n: &str, val: &Expr, in_: &mut Expr) {
    match in_ {
        e @ Expr::Var(_) => {
            if let Expr::Var(n_) = &e {
                if n == n_ {
                    *e = val.clone();
                }
            }
        }
        Expr::App(e1, e2) => {
            substitute(n, val, e2);
            substitute(n, val, e1);
        }
        Expr::Abs(n_, e) => {
            if n_ != n {
                substitute(n, val, e);
            }
        }
        Expr::Let(n_, e1, e2) => {
            substitute(n, val, e1);
            if n != n_ {
                substitute(n, val, e2);
            }
        }
        _ => {}
    }
}

pub fn eval(expr: Expr) -> Expr {
    match expr {
        Expr::Var(n) => Expr::Var(n),
        Expr::App(e1, e2) => {
            let e1 = eval(*e1);
            let e2 = eval(*e2);

            if let Expr::Abs(n, mut e) = e1 {
                substitute(&n, &e2, &mut e);
                *e
            } else {
                Expr::App(Box::new(e1), Box::new(e2))
            }
        }
        Expr::Abs(n, e) => Expr::Abs(n, Box::new(eval(*e))),
        Expr::Lit(n) => Expr::Lit(n),
        Expr::Let(n, val, mut in_) => {
            let val = eval(*val);
            substitute(&n, &val, &mut in_);
            *in_
        }
        Expr::Match(_, _) => todo!(),
    }
}
