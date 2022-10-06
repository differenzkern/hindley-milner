use chumsky::{
    error::Cheap,
    prelude::*,
    text::{newline, Character},
    Error, Stream,
};
use std::{
    fmt::Display,
    ops::{Deref, Range},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    start: usize,
    end: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Spanned<T>(T, Span);

impl<T> Deref for Spanned<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> std::ops::DerefMut for Spanned<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T> Spanned<T> {
    fn span(&self) -> Span {
        self.1
    }
}

impl Into<Span> for std::ops::Range<usize> {
    fn into(self) -> Span {
        Span {
            start: self.start,
            end: self.end,
        }
    }
}

impl Into<std::ops::Range<usize>> for Span {
    fn into(self) -> std::ops::Range<usize> {
        self.start..self.end
    }
}

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
    Indent(usize),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Op {
    Pipeline,
    Plus,
    Minus,
    Mult,
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
            Token::Op(_) => todo!(),
            Token::Indent(level) => {
                "\n".fmt(f)?;
                " ".repeat(*level).fmt(f)
            }
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
    one_of("|()=λ.→_><[]{}").map(Token::Ctrl)
}

pub fn constants() -> impl Parser<char, Token, Error = Simple<char>> {
    text::int(10).map(Token::Num)
}

pub fn lexer() -> impl Parser<char, Vec<Spanned<Token>>, Error = Simple<char>> {
    let single_token = constants()
        .or(ops())
        .or(ctrl())
        .or(keywords())
        .or(type_identifier())
        .or(variable_identifier())
        .map_with_span(|token, span| Spanned(token, span.into()));

    let test = [
        ("fun", Token::Function),
        ("type", Token::Adt),
        ("=", Token::Ctrl('=')),
        ("match", Token::Match),
        ("in", Token::In),
        ("let", Token::Let),
        ("Bool", Token::Type("Bool".to_string())),
        ("x", Token::Ident("x".to_string())),
    ];

    for (test, exp) in test {
        assert_eq!(single_token.parse(test).unwrap().0, exp);
    }

    let line_ws = filter::<_, _, Simple<char>>(|c: &char| *c == ' ' || *c == '\t');

    let line = line_ws
        .ignored()
        .repeated()
        .map_with_span(|ws, span| Spanned(Token::Indent(ws.len()), span.into()))
        .chain(
            single_token
                .separated_by(line_ws)
        ).then_ignore(end().or(newline()));

    recursive(|lines| {
        end()
            .map(|()| vec![])
            .or(line.chain(end().map(|()| vec![]).or(lines)))
    })
}
