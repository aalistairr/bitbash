use proc_macro2::Span;
use syn::parse::{Parse, ParseStream, Result};
use syn::punctuated::Punctuated;
use syn::{braced, parse_quote, token, Error};
use syn::{Attribute, Expr, Ident, ItemStruct, RangeLimits, Token, Type, Visibility};

pub mod kw {
    syn::custom_keyword!(field);
}

#[derive(Clone)]
pub struct Bitfield {
    pub strukt: ItemStruct,
    pub fields: Vec<Field>,
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
        Ok(Bitfield {
            strukt: input.parse()?,
            fields: {
                let mut fields = Vec::new();
                while !input.is_empty() {
                    fields.push(input.parse()?);
                }
                fields
            },
        })
    }
}

impl Parse for Field {
    fn parse(input: ParseStream) -> Result<Field> {
        Ok(Field {
            attrs: input.call(Attribute::parse_outer)?,
            vis: input.parse()?,
            field_token: input.parse()?,
            name: input.parse()?,
            colon_token: input.parse()?,
            value_ty: input.parse()?,
            composition: input.parse()?,
        })
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
