use chumsky::{prelude::*, text::newline};
use std::{fmt::Display, ops::Range};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Spanned<T>(pub T, pub std::ops::Range<usize>);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]

pub enum Token {
    Op(Op),
    Type(String),
    Ident(String),
    Match,
    Function,
    Adt,
    Ctrl(char),
    Num(String),
    Let,
    In,
    EOF
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Op {
    Pipeline,
    Plus,
    Minus,
    Mult,
}

impl Display for Op {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Op::Pipeline => "|>".fmt(f),
            Op::Plus => "+".fmt(f),
            Op::Minus => "-".fmt(f),
            Op::Mult => "*".fmt(f),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Constant {
    UInt(u128),
    String(String),
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::Match => "match".fmt(f),
            Token::Function => "fun".fmt(f),
            Token::Adt => "type".fmt(f),
            Token::Ctrl(c) => c.fmt(f),
            Token::Ident(ident) => ident.fmt(f),
            Token::Num(num) => num.fmt(f),
            Token::Let => "let".fmt(f),
            Token::In => "in".fmt(f),
            Token::Type(ident) => ident.fmt(f),
            Token::EOF => "EOF".fmt(f),
            Token::Op(op) => op.fmt(f),
        }
    }
}

pub fn keywords() -> impl Parser<char, Token, Error = Simple<char>> {
    text::ident().try_map(
        |ident: String, span: std::ops::Range<usize>| match ident.as_str() {
            "fun" => Ok(Token::Function),
            "type" => Ok(Token::Adt),
            "match" => Ok(Token::Match),
            "let" => Ok(Token::Let),
            "in" => Ok(Token::In),
            _ => Err(Simple::custom(span, "unknown keyword")),
        },
    )
}

pub fn ops() -> impl Parser<char, Token, Error = Simple<char>> {
    let pipeline = just("|>").to(Op::Pipeline);
    let plus = just("+").to(Op::Plus);
    let minus = just("-").to(Op::Minus);
    let mult = just("*").to(Op::Mult);

    pipeline.or(plus).or(minus).or(mult).map(Token::Op)
}

pub fn type_identifier() -> impl Parser<char, Token, Error = Simple<char>> {
    text::ident().try_map(|ident: String, span| {
        if ident.chars().next().unwrap().is_uppercase() {
            Ok(Token::Type(ident))
        } else {
            Err(Simple::custom(
                span,
                "type identifiers start with an uppercase letter",
            ))
        }
    })
}

pub fn variable_identifier() -> impl Parser<char, Token, Error = Simple<char>> {
    text::ident().try_map(|ident: String, span| {
        if ident.chars().next().unwrap().is_lowercase() {
            Ok(Token::Ident(ident))
        } else {
            Err(Simple::custom(
                span,
                "function and variable identifiers start with a lowercase letter",
            ))
        }
    })
}

pub fn ctrl() -> impl Parser<char, Token, Error = Simple<char>> {
    one_of("|()=λ.→_><[]{}\n\r").map(Token::Ctrl)
}

pub fn constants() -> impl Parser<char, Token, Error = Simple<char>> {
    text::int(10).map(Token::Num)
}

pub fn lexer() -> impl Parser<char, Vec<(Token, Range<usize>)>, Error = Simple<char>> {
    let single_token = constants()
        .or(ops())
        .or(ctrl())
        .or(keywords())
        .or(type_identifier())
        .or(variable_identifier())
        .map_with_span(|token, span| (token, span));

    let line_ws = filter::<_, _, Simple<char>>(|c: &char| *c == ' ' || *c == '\t');

    /*let line = single_token.padded_by(line_ws).repeated().chain(
        newline()
            .or(end())
            .map_with_span(|_, span: Range<usize>| (Token::Ctrl('\n'), span)),
    );*/

    //line.padded_by(text::whitespace()).repeated().flatten()

    single_token.padded_by(line_ws.repeated()).repeated().chain(end().map_with_span(|end, span: Range<usize>| (Token::EOF, span.into())))
}
