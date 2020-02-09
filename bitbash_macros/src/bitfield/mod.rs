use std::ops::Range;

use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;
use syn::parse::Result;
use syn::{parse_macro_input, parse_quote};
use syn::{token, Error, Expr, Fields, ItemStruct, Meta, Path, RangeLimits, Token, Type};

mod output;
mod parse;

use parse::{Composition, Index, Relationship};

fn is_uint(p: &Path) -> bool {
    p.is_ident("usize")
        || p.is_ident("u8")
        || p.is_ident("u16")
        || p.is_ident("u32")
        || p.is_ident("u64")
        || p.is_ident("u128")
}

fn value_repr_ty(value_ty: &Type) -> Type {
    match value_ty {
        Type::Path(t) if is_uint(&t.path) => value_ty.clone(),
        Type::Path(t) if t.path.is_ident("bool") => parse_quote! { u8 },
        _ => parse_quote! {
            <#value_ty as bitbash::ConvertRepr>::Repr
        },
    }
}

fn self_repr_ty(strukt: &ItemStruct, src: &Option<Expr>) -> Type {
    match &strukt.fields {
        Fields::Unnamed(fields) => match &fields.unnamed[0].ty {
            Type::Array(t) => (*t.elem).clone(),
            t => t.clone(),
        },
        Fields::Named(fields) => match &src {
            Some(Expr::Path(p)) => match p.path.get_ident() {
                Some(p) => match fields.named.iter().find(|f| f.ident.as_ref().unwrap() == p) {
                    Some(f) => f.ty.clone(),
                    None => unreachable!(),
                },
                None => unreachable!(),
            },
            _ => unreachable!(),
        },
        Fields::Unit => unreachable!(),
    }
}

fn validate_bits(strukt: &ItemStruct, bits: &parse::Bits) -> Result<()> {
    match &strukt.fields {
        Fields::Unnamed(fields) => match fields.unnamed[0].ty {
            Type::Array(_) if bits.src.is_none() => {
                return Err(Error::new(
                    bits.bracket_token.span,
                    "missing an array index",
                ))
            }
            Type::Array(_) => Ok(()),
            _ if bits.src.is_some() => {
                return Err(Error::new_spanned(&bits.src, "unexpected array index"))
            }
            _ => Ok(()),
        },
        Fields::Named(fields) => match &bits.src {
            None => return Err(Error::new(bits.bracket_token.span, "missing a field")),
            Some(Expr::Path(p))
                if fields
                    .named
                    .iter()
                    .filter_map(|field| field.ident.as_ref())
                    .find(|field_name| p.path.is_ident(&*field_name.to_string()))
                    .is_some() =>
            {
                Ok(())
            }
            _ => return Err(Error::new_spanned(&bits.src, "invalid field")),
        },
        Fields::Unit => unreachable!(),
    }
}

fn into_output_spec(bitfield: parse::Bitfield, use_const: bool) -> Result<output::Bitfield> {
    let strukt = bitfield.strukt;
    match strukt.fields {
        Fields::Unnamed(fields) if fields.unnamed.len() != 1 => {
            return Err(Error::new_spanned(
                fields,
                "a tuple struct may have only one field",
            ))
        }
        Fields::Unit => return Err(Error::new_spanned(strukt, "unit structs are not supported")),
        _ => (),
    }
    let mut fields = Vec::new();
    for field in bitfield.fields {
        fields.push(into_output_field(&strukt, field)?);
    }
    Ok(output::Bitfield {
        use_const,
        strukt,
        fields,
    })
}

fn into_output_field(bitfield: &ItemStruct, field: parse::Field) -> Result<output::Field> {
    let parse::Field {
        attrs: in_attrs,
        vis,
        name,
        value_ty,
        mut composition,
        ..
    } = field;

    let mut out_attrs = Vec::new();
    for attr in in_attrs {
        out_attrs.push(match attr.parse_meta()? {
            Meta::Path(p) if p.is_ident("ro") => output::Attribute::ReadOnly,
            Meta::Path(p) if p.is_ident("private_write") => output::Attribute::PrivateWrite,
            _ => return Err(Error::new_spanned(attr, "invalid attribute")),
        });
    }

    fn fill_in_range(index: &mut Index, ty: &Type) {
        if let Index::Range {
            start: ref mut x @ None,
            ..
        } = index
        {
            *x = Some(parse_quote! { 0 });
        }
        if let Index::Range {
            end: ref mut x @ None,
            ..
        } = index
        {
            *x = Some(parse_quote! { ((core::mem::size_of::<#ty>() * 8) as u32) });
        }
    }

    match &mut composition {
        Composition::Mapping { relationships, .. } => {
            for relationship in relationships {
                if let Some(src) = &relationship.from.src {
                    return Err(Error::new_spanned(
                        src,
                        "the value index must refer only to bits",
                    ));
                }
                let value_repr_ty = value_repr_ty(&value_ty);
                fill_in_range(&mut relationship.from.index, &value_repr_ty);
                validate_bits(bitfield, &relationship.to)?;
                let self_repr_ty = self_repr_ty(bitfield, &relationship.to.src);
                fill_in_range(&mut relationship.to.index, &self_repr_ty);
            }
        }
        Composition::Concatenation { bits, .. } => {
            for bits in bits {
                validate_bits(bitfield, bits)?;
                let self_repr_ty = self_repr_ty(bitfield, &bits.src);
                fill_in_range(&mut bits.index, &self_repr_ty);
            }
        }
    }

    let relationships = match composition {
        Composition::Mapping { relationships, .. } => relationships.into_iter().collect(),
        Composition::Concatenation { bits, .. } => {
            let mut relationships = Vec::new();
            let mut prev_end = parse_quote! { 0 };
            for bits in bits {
                let next_end: Expr = match &bits.index {
                    Index::One(_) => parse_quote! { (#prev_end + 1) },
                    Index::Range {
                        start: Some(start),
                        limits: RangeLimits::HalfOpen(_),
                        end: Some(end),
                    } => parse_quote! { (#prev_end + (#end - #start)) },
                    Index::Range {
                        start: Some(start),
                        limits: RangeLimits::Closed(_),
                        end: Some(end),
                    } => parse_quote! { (#prev_end + (1 + #end - #start)) },
                    _ => unreachable!(),
                };
                let from_index = Index::Range {
                    start: Some(prev_end),
                    limits: RangeLimits::HalfOpen(Token![..](Span::call_site())),
                    end: Some(next_end.clone()),
                };
                relationships.push(Relationship {
                    from: parse::Bits {
                        src: None,
                        bracket_token: token::Bracket {
                            span: Span::call_site(),
                        },
                        index: from_index,
                    },
                    arrow_token: Token![=>](Span::call_site()),
                    to: bits,
                });
                prev_end = next_end;
            }
            relationships
        }
    };

    let mut mapping = Vec::new();
    for mut relationship in relationships {
        fn fix_range(index: &mut Index) {
            if let Index::Range {
                limits: ref mut l @ RangeLimits::Closed(_),
                end: Some(ref mut end),
                ..
            } = index
            {
                *l = RangeLimits::HalfOpen(Token![..](Span::call_site()));
                *end = parse_quote! { (#end + 1) };
            }
        }
        fix_range(&mut relationship.from.index);
        fix_range(&mut relationship.to.index);

        fn get_range(index: Index) -> Range<Expr> {
            match index {
                Index::One(start) => {
                    let end = parse_quote! { (#start + 1) };
                    start..end
                }
                Index::Range {
                    start: Some(start),
                    limits: RangeLimits::HalfOpen(_),
                    end: Some(end),
                } => start..end,
                _ => unreachable!(),
            }
        }

        let from = get_range(relationship.from.index);
        let to_src = relationship.to.src;
        let to = get_range(relationship.to.index);
        mapping.push(output::Relationship { from, to_src, to });
    }

    Ok(output::Field {
        attrs: out_attrs,
        vis,
        name,
        value_ty,
        rels: mapping,
    })
}

pub fn bitfield(input: TokenStream, use_const: bool) -> TokenStream {
    let bitfield = parse_macro_input!(input as parse::Bitfield);
    let bitfield = match into_output_spec(bitfield, use_const) {
        Ok(data) => data,
        Err(err) => return TokenStream::from(err.to_compile_error()),
    };
    let expanded = quote! {
        #bitfield
    };
    TokenStream::from(expanded)
}
