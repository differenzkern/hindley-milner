#![feature(iterator_try_collect)]
use std::rc::Rc;

use ariadne::Source;
use check::check::TIState;
use syntax::ast::Toplevel;

use crate::check::{env::ExprPrinter, expr::EvalContext, r#type::TypePrinter};

pub mod check;
pub mod compile;
pub mod syntax;

fn main() -> std::io::Result<()> {
    let args: Vec<String> = std::env::args().collect();

    if args.len() != 2 {
        println!("expected input file as argument");

        std::process::exit(-1);
    }

    let input = std::fs::read_to_string(&args.get(1).unwrap()).unwrap();

    let toplevel = self::syntax::parse(input.as_str());

    let mut ti = TIState::default();

    for toplevel in toplevel {
        if let Err(report) = match toplevel {
            Toplevel::Adt(def) => ti.check_adt(def),
            Toplevel::Fun(fun) => {
                let name = fun.name.clone();

                match ti.check_fun(fun) {
                    Ok(ty) => {
                        println!("{name}: {}", TypePrinter(ti.env(), &ty));
                        Ok(())
                    }
                    Err(report) => Err(report),
                }
            }
            Toplevel::Expr(expr) => match ti.check_exp(&Rc::new(expr)) {
                Ok((mut expr, ty)) => {
                    let ctx = EvalContext::new(ti.env());
                    let expr = ctx.eval(&mut expr);

                    if let Some(expr) = expr {
                        print!("{}", ExprPrinter(ti.env(), &expr, 0));
                    } else {
                        print!("- ");
                    }

                    println!(": {}", TypePrinter(ti.env(), &ty));
                    Ok(())
                }
                Err(report) => Err(report),
            },
        } {
            report.eprint(Source::from(&input))?;
        }
    }

    Ok(())
}
