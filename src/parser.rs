use anyhow::Result;
use chumsky::prelude::*;

use crate::{Clause, Constructor, Expr, Function, Inductive, Literal, Toplevel};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]

pub enum Token {
    Match,
    Function,
    Inductive,
    Ctrl(char),
    Ident(String),
    True,
    False,
    Num(String),
    Let,
    In,
}

fn lexer() -> impl Parser<char, Vec<Token>, Error = Simple<char>> {
    let num = text::int(10).map(Token::Num);

    let ctrl = one_of("|()=λ.→").map(Token::Ctrl);
    let ident = text::ident().map(|ident: String| match ident.as_str() {
        "fun" => Token::Function,
        "type" => Token::Inductive,
        "match" => Token::Match,
        "true" => Token::True,
        "false" => Token::False,
        _ => Token::Ident(ident),
    });

    let token = num.or(ctrl).or(ident);

    token.padded().repeated()
}

fn parser() -> impl Parser<Token, Vec<Toplevel>, Error = Simple<Token>> {
    let expr = recursive(|expr| {
        let brackets = expr
            .clone()
            .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')')));

        let val = select! {
            Token::True => Expr::Lit(Literal::Bool(true)),
            Token::False => Expr::Lit(Literal::Bool(false)),
            Token::Num(n) => Expr::Lit(Literal::Num(n.parse::<u64>().unwrap()))
        };

        let ident = select! { Token::Ident(ident) => ident };

        let r#let = just(Token::Let)
            .ignore_then(ident)
            .then_ignore(just(Token::Ctrl('=')))
            .then(expr.clone())
            .then_ignore(just(Token::In))
            .then(expr.clone())
            .map(|((name, val), expr)| Expr::Let(name, Box::new(val), Box::new(expr)));

        let lambda = just(Token::Ctrl('λ'))
            .ignore_then(ident)
            .then_ignore(just(Token::Ctrl('.')))
            .then(expr.clone())
            .map(|(a, b)| Expr::Abs(a, Box::new(b)));

        let clause = just(Token::Ctrl('|'))
            .ignore_then(ident)
            .then(ident.repeated())
            .then_ignore(just(Token::Ctrl('→')))
            .then(expr.clone())
            .map(|((constructor, variables), expr)| Clause {
                constructor,
                variables,
                expr,
            });

        let r#match = just(Token::Match)
            .ignore_then(ident)
            .then(clause.repeated())
            .map(|(variable, clauses)| Expr::Match(variable, clauses));

        let atom = brackets
            .or(val)
            .or(r#let)
            .or(lambda)
            .or(r#match)
            .or(ident.map(Expr::Var));

        atom.clone().then(atom.repeated()).map(|(atom, rem)| {
            rem.into_iter().fold(atom, |left, right| {
                Expr::App(Box::new(left), Box::new(right))
            })
        })
    });

    let ident = select!(Token::Ident(ident) => ident);

    let function = just(Token::Function)
        .ignore_then(ident)
        .then(ident.repeated())
        .then_ignore(just(Token::Ctrl('=')))
        .then(expr.clone())
        .map(|((name, arguments), body)| {
            Toplevel::Fun(Function {
                name,
                arguments,
                body,
            })
        });

    let constructor = select!(Token::Ident(constructor) => constructor)
        .then(ident.repeated())
        .map(|(name, arguments)| Constructor { name, arguments });

    let inductive = just(Token::Inductive)
        .ignore_then(ident)
        .then_ignore(just(Token::Ctrl('=')))
        .then(constructor.separated_by(just(Token::Ctrl('|'))))
        .map(|(name, constructors)| Toplevel::Ind(Inductive { name, constructors }));

    function
        .or(inductive)
        .or(expr.clone().map(Toplevel::Expr))
        .repeated()
}

pub fn parse(s: &str) -> Result<Vec<Toplevel>> {
    let tokens = lexer().parse(s).map_err(|err| anyhow::anyhow!("{err:?}"))?;
    parser()
        .parse(tokens)
        .map_err(|err| anyhow::anyhow!("{err:?}"))
}
