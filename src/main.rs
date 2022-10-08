use std::rc::Rc;

use ariadne::Source;
use check::check::TIState;
use parse::ast::Toplevel;


pub mod parse;
pub mod check;

#[macro_export]
macro_rules! cast {
    ($target: expr, $pat: path) => {
        {
            if let $pat(a) = $target { // #1
                a
            } else {
                panic!(
                    "mismatch variant when cast to {}", 
                    stringify!($pat)); // #2
            }
        }
    };
}

fn main() -> std::io::Result<()> {
    let args: Vec<String> = std::env::args().collect();

    if args.len() != 2 {
        println!("expected input file as argument");

        std::process::exit(-1);
    }

    let input = std::fs::read_to_string(&args.get(1).unwrap()).unwrap();


    let toplevel = self::parse::parser::parse(input.as_str());

    let mut ti = TIState::default();

    for toplevel in toplevel {
        if let Err(report) = match toplevel {
            Toplevel::Adt(def) => ti.check_adt(def),
            Toplevel::Fun(fun) => match ti.check_fun(fun) {
                Ok(ty) => {
                    println!("{ty:#?}");
                    Ok(())
                }
                Err(report) => Err(report),
            },
            Toplevel::Expr(expr) => match ti.check_exp(&Rc::new(expr)) {
                Ok(ty) => {
                    println!("{ty:#?}");
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

