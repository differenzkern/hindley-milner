use std::{rc::Rc, ops::Deref, fmt::Display};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Toplevel {
    Adt(AdtDef),
    Fun(FunctionDef),
    Expr(Spanned<Ast>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdtDef {
    pub name: Rc<str>,
    pub constructors: Vec<Constructor>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Constructor {
    pub name: Rc<str>,
    pub arguments: Vec<Rc<str>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionDef {
    pub name: Rc<str>,
    pub arguments: Vec<Rc<str>>,
    pub body: Rc<Spanned<Ast>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ast {
    Var(Rc<str>),
    App(Rc<Spanned<Ast>>, Rc<Spanned<Ast>>),
    Abs(Rc<str>, Rc<Spanned<Ast>>),
    Lit(Literal),
    Let(Rc<str>, Rc<Spanned<Ast>>, Rc<Spanned<Ast>>),
    Match(Spanned<Rc<str>>, Vec<Spanned<Clause>>),
}

#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Clause {
    pub constructor: Spanned<Rc<str>>,
    pub variables: Vec<Spanned<Rc<str>>>,
    pub expr: Rc<Spanned<Ast>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Literal {
    Num(u64),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl chumsky::span::Span for Span {
    type Context = ();

    type Offset = usize;

    fn new(_: Self::Context, range: std::ops::Range<Self::Offset>) -> Self {
        Self {
            start: range.start,
            end: range.end
        }
    }

    fn context(&self) -> Self::Context {
        ()
    }

    fn start(&self) -> Self::Offset {
        self.start
    }

    fn end(&self) -> Self::Offset {
        self.end
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Spanned<T>(pub T, pub Span);

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

impl<T: Display> Display for Spanned<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<T> Spanned<T> {
    pub fn span(&self) -> Span {
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

impl Display for Ast {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn fmt_parens(this: &Ast, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match this {
                this @ Ast::App(_, _) => write!(f, "({this})"),
                Ast::Abs(_, _) => write!(f, "({this})"),
                Ast::Let(_, _, _) => write!(f, "({this})"),
                _ => this.fmt(f),
            }
        }

        match self {
            Ast::Var(name) => write!(f, "{name}"),
            Ast::App(e1, e2) => {
                write!(f, "{e1} ")?;
                fmt_parens(e2, f)
            }
            Ast::Abs(x, e) => {
                write!(f, "λ{x}.")?;
                fmt_parens(e, f)
            }
            Ast::Lit(lit) => write!(f, "{lit}"),
            Ast::Let(x, e1, e2) => {
                write!(f, "let {x} = {e1} in {e2}")
            }
            Ast::Match(x, clauses) => {
                write!(f, "match {x}")?;
                for clause in clauses {
                    write!(f, "{clause}")?;
                }
                Ok(())
            }
        }
    }
}

impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Literal::Num(x) => write!(f, "{x}"),
        }
    }
}

impl Display for Clause {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Clause {
            constructor,
            variables,
            expr,
        } = self;

        write!(f, " | {constructor}")?;

        for var in variables {
            write!(f, " {var}")?;
        }

        write!(f, " → {expr}")
    }
}
