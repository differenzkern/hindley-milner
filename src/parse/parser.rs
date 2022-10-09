use std::ops::Range;
use std::rc::Rc;

use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};
use chumsky::{prelude::*, Stream};

use super::ast::{AdtDef, Ast, Clause, Constructor, FunctionDef, Literal, Spanned, Toplevel};

use super::lexer::{lexer, Token};

pub fn parse(src: &str) -> Vec<Toplevel> {
    let len = src.chars().count();

    let (tokens, tokenize_errs) = lexer().parse_recovery(src);

    let (toplevel, parse_errs) = spanned_parser()
        .padded_by(just(Token::Ctrl('\n')).repeated())
        .repeated()
        .then_ignore(just(Token::EOF))
        .parse_recovery(Stream::from_iter(
            len..len,
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

fn spanned_parser() -> impl Parser<Token, Toplevel, Error = Simple<Token>> {
    let expr = recursive(|expr| {
        let brackets = expr
            .clone()
            .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')')));

        let val = select! {
            Token::Num(n) => Ast::Lit(Literal::Num(n.parse::<u64>().unwrap()))
        };

        let ident = select! { Token::Ident(ident) => ident, Token::Type(ident) => ident };

        let spanned_ident = ident
            .map(Rc::from)
            .map_with_span(|ident, span: Range<usize>| Spanned(ident, span.into()));

        let r#let = just(Token::Let)
            .ignore_then(ident)
            .then_ignore(just(Token::Ctrl('=')))
            .then(expr.clone())
            .then_ignore(just(Token::In))
            .then(expr.clone())
            .map(|((name, val), expr)| Ast::Let(Rc::from(name), Rc::new(val), Rc::new(expr)));

        let lambda = just(Token::Ctrl('λ'))
            .ignore_then(ident)
            .then_ignore(just(Token::Ctrl('.')))
            .then(expr.clone())
            .map(|(a, b)| Ast::Abs(Rc::from(a), Rc::new(b)));

        let clause = just(Token::Ctrl('|'))
            .ignore_then(
                ident
                    .map(Rc::from)
                    .map_with_span(|ident, span: Range<usize>| Spanned(ident, span.into())),
            )
            .then(
                ident
                    .map(Rc::from)
                    .map_with_span(|ident, span: Range<usize>| Spanned(ident, span.into()))
                    .repeated(),
            )
            .then_ignore(just(Token::Ctrl('→')))
            .then(expr.clone())
            .map_with_span(|((constructor, variables), expr), span: Range<usize>| {
                Spanned(
                    Clause {
                        constructor,
                        variables,
                        expr: Rc::new(expr),
                    },
                    span.into(),
                )
            });

        let r#match = just(Token::Match)
            .ignore_then(spanned_ident)
            .then(
                clause
                    .padded_by(just(Token::Ctrl('\n')).repeated())
                    .repeated()
                    .delimited_by(just(Token::Ctrl('{')), just(Token::Ctrl('}'))),
            )
            .map(|(variable, clauses)| Ast::Match(variable, clauses));

        let atom = brackets.or(val
            .or(r#let)
            .or(lambda)
            .or(r#match)
            .or(ident.map(Rc::from).map(Ast::Var))
            .map_with_span(|ident, span: Range<usize>| Spanned(ident, span.into())));

        atom.clone().then(atom.repeated()).map(|(atom, rem)| {
            rem.into_iter().fold(atom, |left, right| {
                let span = left.1.start..right.1.end;

                Spanned(Ast::App(Rc::new(left), Rc::new(right)), span.into())
            })
        })
    });

    let ident = select! { Token::Ident(ident) => ident, Token::Type(ident) => ident };

    let function = just(Token::Function)
        .ignore_then(ident.map(Rc::from))
        .then(ident.map(Rc::from).repeated())
        .then_ignore(just(Token::Ctrl('=')))
        .then(expr.clone().map(Rc::from))
        .map(|((name, arguments), body)| {
            Toplevel::Fun(FunctionDef {
                name,
                arguments,
                body,
            })
        });

    let constructor = ident
        .map(Rc::from)
        .then(ident.map(Rc::from).repeated())
        .map(|(name, arguments)| Constructor { name, arguments });

    let adt = just(Token::Adt)
        .ignore_then(ident.map(Rc::from))
        .then_ignore(just(Token::Ctrl('=')))
        .then(constructor.separated_by(just(Token::Ctrl('|'))))
        .map(|(name, constructors)| Toplevel::Adt(AdtDef { name, constructors }));

    function.or(adt).or(expr.clone().map(Toplevel::Expr))
}
