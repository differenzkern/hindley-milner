use anyhow::Result;
use chumsky::prelude::*;

use crate::{Expr, Literal};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Token {
    Let,
    In,
    Lambda,
    Ident(String),
    True,
    False,
    Num(String),
    Bracket(char),
    Dot,
    Op(char),
}

fn lexer() -> impl Parser<char, Vec<Token>, Error = Simple<char>> {
    let num = text::int(10).map(Token::Num);

    let ctrl = one_of("λ.=()").map(|c| match c {
        'λ' => Token::Lambda,
        '=' => Token::Op('='),
        '(' => Token::Bracket('('),
        ')' => Token::Bracket(')'),
        '.' => Token::Dot,
        _ => panic!(),
    });

    let ident = text::ident().map(|ident: String| match ident.as_str() {
        "let" => Token::Let,
        "in" => Token::In,
        "true" => Token::True,
        "false" => Token::False,
        _ => Token::Ident(ident),
    });

    let token = num
        .or(ctrl)
        .or(ident)
        .recover_with(skip_then_retry_until([]));

    token.padded().repeated()
}

fn expr_parser() -> impl Parser<Token, Expr, Error = Simple<Token>> + Clone {
    recursive(|expr| {
        let brackets = expr
            .clone()
            .delimited_by(just(Token::Bracket('(')), just(Token::Bracket(')')));

        let val = select! {
            Token::True => Expr::Lit(Literal::Bool(true)),
            Token::False => Expr::Lit(Literal::Bool(false)),
            Token::Num(n) => Expr::Lit(Literal::Num(n.parse::<u64>().unwrap()))
        };

        let ident = select! { Token::Ident(ident) => ident };

        let let_ = just(Token::Let)
            .ignore_then(ident)
            .then_ignore(just(Token::Op('=')))
            .then(expr.clone())
            .then_ignore(just(Token::In))
            .then(expr.clone())
            .map(|((name, val), expr)| Expr::Let(name, Box::new(val), Box::new(expr)));

        let lambda = just(Token::Lambda)
            .ignore_then(ident)
            .then_ignore(just(Token::Dot))
            .then(expr.clone())
            .map(|(a, b)| Expr::Abs(a, Box::new(b)));

        let atom = brackets
            .or(val)
            .or(let_)
            .or(lambda)
            .or(ident.map(Expr::Var));

        atom.clone().then(atom.repeated()).map(|(atom, rem)| {
            rem.into_iter().fold(atom, |left, right| {
                Expr::App(Box::new(left), Box::new(right))
            })
        })
    })
}

pub fn parse(s: &str) -> Result<Expr> {
    let tokens = lexer().parse(s).map_err(|err| anyhow::anyhow!("{err:?}"))?;
    expr_parser()
        .parse(tokens)
        .map_err(|err| anyhow::anyhow!("{err:?}"))
}
