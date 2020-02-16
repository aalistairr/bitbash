use proc_macro2::Span;
use syn::parse::{Parse, ParseStream, Result};
use syn::punctuated::Punctuated;
use syn::{braced, parenthesized, parse_quote, token, Error};
use syn::{Attribute, Expr, Ident, ItemStruct, RangeLimits, Token, Type, Visibility};

pub mod kw {
    syn::custom_keyword!(field);
    syn::custom_keyword!(new);
    syn::custom_keyword!(derive_debug);
}

#[derive(Clone)]
pub struct Bitfield {
    pub strukt: ItemStruct,
    pub new: Option<New>,
    pub derive_debug: Option<DeriveDebug>,
    pub fields: Vec<Field>,
}

#[derive(Clone)]
pub struct New {
    pub attrs: Vec<Attribute>,
    pub vis: Visibility,
    pub new_token: kw::new,
    pub paren_token: token::Paren,
    pub init_fields: Punctuated<Ident, Token![,]>,
    pub semi_token: Token![;],
}

#[derive(Clone)]
pub struct DeriveDebug {
    pub attrs: Vec<Attribute>,
    pub derive_debug_token: kw::derive_debug,
    pub semi_token: Token![;],
}

#[derive(Clone)]
pub struct Field {
    pub attrs: Vec<Attribute>,
    pub vis: Visibility,
    pub field_token: kw::field,
    pub name: Ident,
    pub colon_token: Token![:],
    pub value_ty: Type,
    pub composition: Composition,
}

#[derive(Clone)]
pub enum Composition {
    Concatenation {
        eq_token: Token![=],
        bits: Punctuated<Bits, Token![~]>,
        semi_token: Token![;],
    },
    Mapping {
        brace_token: token::Brace,
        relationships: Punctuated<Relationship, Token![,]>,
    },
}

#[derive(Clone)]
pub struct Relationship {
    pub from: Bits,
    pub arrow_token: Token![=>],
    pub to: Bits,
}

#[derive(Clone)]
pub struct Bits {
    pub src: Option<Expr>,
    pub bracket_token: token::Bracket,
    pub index: Index,
}

#[derive(Clone)]
pub enum Index {
    One(Expr),
    Range {
        start: Option<Expr>,
        limits: RangeLimits,
        end: Option<Expr>,
    },
}

impl Parse for Bitfield {
    fn parse(input: ParseStream) -> Result<Bitfield> {
        let strukt = input.parse()?;
        let mut new = None;
        let mut derive_debug = None;
        let mut fields = Vec::new();
        while !input.is_empty() {
            match input.parse()? {
                Stmt::New(n) if new.is_none() => new = Some(n),
                Stmt::New(n) => {
                    return Err(Error::new_spanned(
                        n.new_token,
                        "multiple definitions of `new`",
                    ))
                }
                Stmt::DeriveDebug(dd) if derive_debug.is_none() => derive_debug = Some(dd),
                Stmt::DeriveDebug(dd) => {
                    return Err(Error::new_spanned(
                        dd.derive_debug_token,
                        "multiple `derive_debug` statements",
                    ))
                }
                Stmt::Field(f) => fields.push(f),
            }
        }
        Ok(Bitfield {
            strukt,
            new,
            derive_debug,
            fields,
        })
    }
}

enum Stmt {
    New(New),
    DeriveDebug(DeriveDebug),
    Field(Field),
}

impl Parse for Stmt {
    fn parse(input: ParseStream) -> Result<Stmt> {
        let attrs = input.call(Attribute::parse_outer)?;
        let vis = input.parse()?;
        if let Ok(new_token) = input.parse() {
            let content;
            Ok(Stmt::New(New {
                attrs,
                vis,
                new_token,
                paren_token: parenthesized!(content in input),
                init_fields: Punctuated::parse_terminated(&content)?,
                semi_token: input.parse()?,
            }))
        } else if let Ok(derive_debug_token) = input.parse() {
            Ok(Stmt::DeriveDebug(DeriveDebug {
                attrs,
                derive_debug_token,
                semi_token: input.parse()?,
            }))
        } else {
            Ok(Stmt::Field(Field {
                attrs,
                vis,
                field_token: input.parse()?,
                name: input.parse()?,
                colon_token: input.parse()?,
                value_ty: input.parse()?,
                composition: input.parse()?,
            }))
        }
    }
}

impl Parse for Composition {
    fn parse(input: ParseStream) -> Result<Composition> {
        if input.peek(Token![=]) {
            Ok(Composition::Concatenation {
                eq_token: input.parse()?,
                bits: Punctuated::parse_separated_nonempty(input)?,
                semi_token: input.parse()?,
            })
        } else {
            let content;
            Ok(Composition::Mapping {
                brace_token: braced!(content in input),
                relationships: Punctuated::parse_terminated(&content)?,
            })
        }
    }
}

impl Parse for Relationship {
    fn parse(input: ParseStream) -> Result<Relationship> {
        Ok(Relationship {
            from: input.parse()?,
            arrow_token: input.parse()?,
            to: input.parse()?,
        })
    }
}

impl Parse for Bits {
    fn parse(input: ParseStream) -> Result<Bits> {
        match input.parse()? {
            Expr::Index(x) => Ok(Bits {
                src: Some(*x.expr),
                bracket_token: x.bracket_token,
                index: Index::from_expr(*x.index)?,
            }),
            Expr::Array(mut x) if x.elems.len() == 1 => Ok(Bits {
                src: None,
                bracket_token: x.bracket_token,
                index: Index::from_expr(x.elems.pop().unwrap().into_value())?,
            }),
            Expr::Array(x) => Err(Error::new_spanned(x, "expected an array with one element")),
            expr => Ok(Bits {
                src: Some(expr),
                bracket_token: token::Bracket {
                    span: Span::call_site(),
                },
                index: Index::Range {
                    start: None,
                    limits: RangeLimits::HalfOpen(Token![..](Span::call_site())),
                    end: None,
                },
            }),
        }
    }
}

impl Index {
    pub fn from_expr(expr: Expr) -> Result<Index> {
        fn parens(x: Expr) -> Expr {
            parse_quote! { (#x) }
        }
        match expr {
            Expr::Range(x) => Ok(Index::Range {
                start: x.from.map(|x| *x).map(parens),
                limits: x.limits,
                end: x.to.map(|x| *x).map(parens),
            }),
            expr => Ok(Index::One(expr)),
        }
    }
}
