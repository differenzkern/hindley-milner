use std::{fmt::Display, ops::Deref, rc::Rc};

use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};
use chumsky::{prelude::*, Stream};

use crate::{Algebraic, Clause, Constructor, Expr, Function, Literal, Toplevel};

pub type Span = std::ops::Range<usize>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Spanned<T>(pub T, pub Span);

impl<T> Spanned<T> {
    pub fn span(&self) -> Span {
        self.1.clone()
    }
}

impl<T> Deref for Spanned<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: Display> Display for Spanned<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]

pub enum Token {
    Match,
    Function,
    Inductive,
    Ctrl(char),
    Ident(String),
    Num(String),
    Newline,
    Let,
    In,
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::Match => "match".fmt(f),
            Token::Function => "fun".fmt(f),
            Token::Inductive => "type".fmt(f),
            Token::Ctrl(c) => c.fmt(f),
            Token::Ident(ident) => ident.fmt(f),
            Token::Num(num) => num.fmt(f),
            Token::Let => "let".fmt(f),
            Token::In => "in".fmt(f),
            Token::Newline => "\n".fmt(f),
        }
    }
}

fn spanned_lexer() -> impl Parser<char, Vec<(Token, Span)>, Error = Simple<char>> {
    let num = text::int(10).map(Token::Num);

    let newline = just("\n")
        .repeated()
        .at_least(1)
        .ignored()
        .map(|_| Token::Newline);
    let ctrl = one_of("|()=λ.→").map(Token::Ctrl);
    let ident = text::ident().map(|ident: String| match ident.as_str() {
        "fun" => Token::Function,
        "type" => Token::Inductive,
        "match" => Token::Match,
        "let" => Token::Let,
        "in" => Token::In,
        _ => Token::Ident(ident),
    });

    let token = num
        .or(ctrl)
        .or(ident)
        .or(newline)
        .recover_with(skip_then_retry_until([]));

    let comment = just("/*").then(take_until(just("*/")));

    token
        .map_with_span(|token, span| (token, span))
        .padded_by(one_of(" \t").repeated())
        .padded_by(comment.repeated())
        .repeated()
}

fn spanned_parser() -> impl Parser<Token, Toplevel, Error = Simple<Token>> {
    let expr = recursive(|expr| {
        let brackets = expr
            .clone()
            .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')')));

        let val = select! {
            Token::Num(n) => Expr::Lit(Literal::Num(n.parse::<u64>().unwrap()))
        };

        let ident = select! { Token::Ident(ident) => ident };

        let spanned_ident = ident.map(Rc::from).map_with_span(Spanned);

        let r#let = just(Token::Let)
            .ignore_then(ident)
            .then_ignore(just(Token::Ctrl('=')))
            .then(expr.clone())
            .then_ignore(just(Token::In))
            .then(expr.clone())
            .map(|((name, val), expr)| Expr::Let(Rc::from(name), Rc::new(val), Rc::new(expr)));

        let lambda = just(Token::Ctrl('λ'))
            .ignore_then(ident)
            .then_ignore(just(Token::Ctrl('.')))
            .then(expr.clone())
            .map(|(a, b)| Expr::Abs(Rc::from(a), Rc::new(b)));

        let clause = just(Token::Ctrl('|'))
            .ignore_then(ident.map(Rc::from).map_with_span(Spanned))
            .then(ident.map(Rc::from).map_with_span(Spanned).repeated())
            .then_ignore(just(Token::Ctrl('→')))
            .then(expr.clone())
            .map_with_span(|((constructor, variables), expr), span| {
                Spanned(
                    Clause {
                        constructor,
                        variables,
                        expr: Rc::new(expr),
                    },
                    span,
                )
            });

        let r#match = just(Token::Match)
            .ignore_then(spanned_ident)
            .then(clause.repeated())
            .map(|(variable, clauses)| Expr::Match(variable, clauses));

        let atom = brackets.or(val
            .or(r#let)
            .or(lambda)
            .or(r#match)
            .or(ident.map(Rc::from).map(Expr::Var))
            .map_with_span(Spanned));

        atom.clone().then(atom.repeated()).map(|(atom, rem)| {
            rem.into_iter().fold(atom, |left, right| {
                let span = left.1.start..right.1.end;

                Spanned(Expr::App(Rc::new(left), Rc::new(right)), span)
            })
        })
    });

    let ident = select!(Token::Ident(ident) => ident);

    let function = just(Token::Function)
        .ignore_then(ident.map(Rc::from))
        .then(ident.map(Rc::from).repeated())
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
        .map(Rc::from)
        .then(ident.map(Rc::from).repeated())
        .map(|(name, arguments)| Constructor { name, arguments });

    let inductive = just(Token::Inductive)
        .ignore_then(ident.map(Rc::from))
        .then_ignore(just(Token::Ctrl('=')))
        .then(constructor.separated_by(just(Token::Ctrl('|'))))
        .map(|(name, constructors)| Toplevel::Algebraic(Algebraic { name, constructors }));

    function.or(inductive).or(expr.clone().map(Toplevel::Expr))
}

pub fn parse(src: &str) -> Vec<Toplevel> {
    let len = src.chars().count();

    let (tokens, tokenize_errs) = spanned_lexer().parse_recovery(src);

    let (toplevel, parse_errs) = spanned_parser()
        .separated_by(just(Token::Newline).repeated())
        .parse_recovery(Stream::from_iter(
            len..len + 1,
            tokens.unwrap_or_default().into_iter(),
        ));

    tokenize_errs
        .into_iter()
        .map(|e| e.map(|c| c.to_string()))
        .chain(parse_errs.into_iter().map(|e| e.map(|tok| tok.to_string())))
        .for_each(|e| {
            let report = Report::build(ReportKind::Error, (), e.span().start);

            let report = match e.reason() {
                chumsky::error::SimpleReason::Unclosed { span, delimiter } => report
                    .with_message(format!(
                        "Unclosed delimiter {}",
                        delimiter.fg(Color::Yellow)
                    ))
                    .with_label(
                        Label::new(span.clone())
                            .with_message(format!(
                                "Unclosed delimiter {}",
                                delimiter.fg(Color::Yellow)
                            ))
                            .with_color(Color::Yellow),
                    )
                    .with_label(
                        Label::new(e.span())
                            .with_message(format!(
                                "Must be closed before this {}",
                                e.found()
                                    .unwrap_or(&"end of file".to_string())
                                    .fg(Color::Red)
                            ))
                            .with_color(Color::Red),
                    ),
                chumsky::error::SimpleReason::Unexpected => report
                    .with_message(format!(
                        "{}, expected {}",
                        if e.found().is_some() {
                            "Unexpected token in input"
                        } else {
                            "Unexpected end of input"
                        },
                        if e.expected().len() == 0 {
                            "something else".to_string()
                        } else {
                            e.expected()
                                .map(|expected| match expected {
                                    Some(expected) => expected.to_string(),
                                    None => "end of input".to_string(),
                                })
                                .collect::<Vec<_>>()
                                .join(", ")
                        }
                    ))
                    .with_label(
                        Label::new(e.span())
                            .with_message(format!(
                                "Unexpected token {}",
                                e.found()
                                    .unwrap_or(&"end of file".to_string())
                                    .fg(Color::Red)
                            ))
                            .with_color(Color::Red),
                    ),
                chumsky::error::SimpleReason::Custom(msg) => report.with_message(msg).with_label(
                    Label::new(e.span())
                        .with_message(format!("{}", msg.fg(Color::Red)))
                        .with_color(Color::Red),
                ),
            };

            report.finish().print(Source::from(&src)).unwrap();
        });

    toplevel.unwrap_or_default()
}
