use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::{format_ident, quote};
use syn::{parse_macro_input, parse_quote, Data, DeriveInput, Error, Fields, Meta, NestedMeta};

pub fn bitenum(input: TokenStream, use_const: bool) -> TokenStream {
    let DeriveInput {
        vis,
        ident,
        generics,
        data,
        attrs,
        ..
    } = parse_macro_input!(input as DeriveInput);
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let enumm = match data {
        Data::Enum(x) => x,
        _ => {
            return TokenStream::from(
                Error::new(Span::call_site(), "BitEnum only supports `enum`s").to_compile_error(),
            )
        }
    };

    let (mut variant_name, mut variant_discriminant) = (Vec::new(), Vec::new());
    for variant in enumm.variants {
        match variant.fields {
            Fields::Unit => (),
            _ => {
                return TokenStream::from(
                    Error::new_spanned(variant, "variant must have no fields").to_compile_error(),
                )
            }
        }
        let discriminant = match variant.discriminant {
            Some((_, d)) => d,
            None => {
                return TokenStream::from(
                    Error::new_spanned(variant, "variant does not have a discriminant")
                        .to_compile_error(),
                )
            }
        };
        variant_name.push(variant.ident);
        variant_discriminant.push(discriminant);
    }

    let repr = attrs
        .iter()
        .filter(|attr| {
            attr.path.segments.len() == 1 && attr.path.get_ident() == Some(&format_ident!("repr"))
        })
        .next();
    let repr = match repr {
        Some(attr) => match attr.parse_meta() {
            Ok(Meta::List(l)) if l.nested.len() == 1 => match &l.nested[0] {
                NestedMeta::Meta(m) => m.path().clone(),
                _ => {
                    return TokenStream::from(
                        Error::new_spanned(attr, "invalid attr").to_compile_error(),
                    )
                }
            },
            _ => {
                return TokenStream::from(
                    Error::new_spanned(attr, "invalid attr").to_compile_error(),
                )
            }
        },
        None => parse_quote! { isize },
    };

    let mod_name = format_ident!("__BitEnum_{}", ident);
    let mut expanded = quote! {
        #[allow(non_snake_case)]
        mod #mod_name {
            use super::*;

            #(
                #[allow(non_upper_case_globals)]
                pub const #variant_name: #repr = #variant_discriminant;
            )*
        }

        impl #impl_generics bitbash::ConvertRepr for #ident #ty_generics #where_clause {
            type Repr = #repr;

            fn try_from_repr(value: #repr) -> Option<Self> {
                match value {
                    #(#mod_name::#variant_name => Some(#ident::#variant_name),)*
                    _ => None,
                }
            }

            fn into_repr(self) -> #repr {
                self as #repr
            }
        }
    };
    if use_const {
        expanded.extend(quote! {
            impl #impl_generics #ident #ty_generics #where_clause {
                #vis const fn const_try_from_repr(value: #repr) -> Option<Self> {
                    match value {
                        #(#mod_name::#variant_name => Some(#ident::#variant_name),)*
                        _ => None,
                    }
                }

                #vis const fn const_into_repr(self) -> #repr {
                    self as #repr
                }
            }
        });
    }
    TokenStream::from(expanded)
}
