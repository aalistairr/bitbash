use std::ops::Range;

use proc_macro2::TokenStream;
use quote::{format_ident, quote, ToTokens};
use syn::parse_quote;
use syn::{Expr, Fields, Ident, ItemStruct, Path, Token, Type, Visibility};

use super::{is_uint, self_repr_ty, value_repr_ty};
use crate::constness;

#[derive(Clone)]
pub struct Bitfield {
    pub use_const: bool,
    pub strukt: ItemStruct,
    pub new: Option<New>,
    pub fields: Vec<Field>,
}

#[derive(Clone)]
pub struct New {
    pub attrs: Vec<NewAttribute>,
    pub vis: Visibility,
    pub init_field_names: Vec<Ident>,
    pub init_field_tys: Vec<Type>,
}

#[derive(Clone)]
pub enum NewAttribute {
    DisableCheck,
}

#[derive(Clone)]
pub struct Field {
    pub attrs: Vec<FieldAttribute>,
    pub vis: Visibility,
    pub name: Ident,
    pub value_ty: Type,
    pub rels: Vec<Relationship>,
}

#[derive(Clone)]
pub enum FieldAttribute {
    ReadOnly,
    PrivateWrite,
}

#[derive(Clone)]
pub struct Relationship {
    pub from: Range<Expr>,
    pub to_src: Option<Expr>,
    pub to: Range<Expr>,
}

impl ToTokens for Bitfield {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let Bitfield {
            use_const,
            strukt,
            new,
            fields,
        } = self;
        let constness = constness(*use_const);

        let strukt_name = &strukt.ident;
        let (impl_generics, ty_generics, where_clause) = strukt.generics.split_for_impl();

        fn mask(ty: &Type, bits: &Ident) -> Expr {
            parse_quote! {{
                let one: #ty = 1;
                let (shifted_bit, overflowed) = one.overflowing_shl(#bits.end - #bits.start);
                let (mask, _) = shifted_bit.overflowing_sub(1);
                ((overflowed as #ty * !0) | ((!overflowed as #ty) * mask)) << #bits.start
            }}
        }

        fn field_rels<'a>(field: &'a Field) -> Vec<Ident> {
            field
                .rels
                .iter()
                .enumerate()
                .map(|(i, _)| format_ident!("rel_{}", i))
                .collect()
        }

        let mut fields_tokens = quote! {};
        for field in fields {
            let value_ty = &field.value_ty;
            let value_repr_ty = value_repr_ty(value_ty);

            let rels = field_rels(field);

            let mut rels_tokens = quote! {};
            for (rel, rel_name) in field.rels.iter().zip(&rels) {
                let self_repr = match &strukt.fields {
                    Fields::Unnamed(_) => match &rel.to_src {
                        Some(i) => quote! { this.0[#i] },
                        None => quote! { this.0 },
                    },
                    Fields::Named(_) => match &rel.to_src {
                        Some(p) => quote! { this.#p },
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                };

                let inbounds_assertion = match &strukt.fields {
                    Fields::Unnamed(fields) => match &fields.unnamed[0].ty {
                        Type::Array(t) => match &rel.to_src {
                            Some(i) => {
                                let len = &t.len;
                                Some(quote! {
                                    pub const _ASSERT_INBOUNDS: () = assert!(#i < #len);
                                })
                            }
                            _ => unreachable!(),
                        },
                        _ => None,
                    },
                    _ => None,
                };

                let (rel_to_start, rel_to_end) = (&rel.to.start, &rel.to.end);
                let (rel_from_start, rel_from_end) = (&rel.from.start, &rel.from.end);
                let self_repr_ty = self_repr_ty(strukt, &rel.to_src);
                let self_bits = quote! { #rel_to_start..#rel_to_end };
                let value_bits = quote! { #rel_from_start..#rel_from_end };

                let self_mask = mask(&self_repr_ty, &format_ident!("SELF_BITS"));
                let value_mask = mask(&value_repr_ty, &format_ident!("VALUE_BITS"));

                let assert_inbounds = inbounds_assertion.map(|assertion| match use_const {
                    true => quote! { pub const _ASSERT_INBOUNDS: () = #assertion; },
                    false => assertion,
                });
                let assertions = match use_const {
                    true => quote! {
                        pub const _ASSERT0: () = assert!(SELF_BITS.start <= SELF_BITS.end);
                        pub const _ASSERT1: () = assert!(VALUE_BITS.start <= VALUE_BITS.end);
                        pub const _ASSERT2: () = assert!(SELF_BITS_LEN == VALUE_BITS_LEN);
                        pub const _ASSERT3: () = assert!(SELF_BITS.end as usize <= core::mem::size_of::<SelfRepr>() * 8);
                        pub const _ASSERT4: () = assert!(VALUE_BITS.end as usize <= core::mem::size_of::<ValueRepr>() * 8);
                        #assert_inbounds
                    },
                    false => quote! {{
                        assert!(SELF_BITS.start <= SELF_BITS.end);
                        assert!(VALUE_BITS.start <= VALUE_BITS.end);
                        assert!(SELF_BITS_LEN == VALUE_BITS_LEN);
                        assert!(SELF_BITS.end as usize <= core::mem::size_of::<SelfRepr>() * 8);
                        assert!(VALUE_BITS.end as usize <= core::mem::size_of::<ValueRepr>() * 8);
                        #assert_inbounds
                    }},
                };

                rels_tokens.extend(quote! {
                    #[allow(non_snake_case)]
                    pub mod #rel_name {
                        use super::*;

                        pub(in super::super::super) type SelfRepr = #self_repr_ty;

                        pub const SELF_BITS: core::ops::Range<u32> = #self_bits;
                        pub const SELF_BITS_LEN: usize = (SELF_BITS.end - SELF_BITS.start) as usize;
                        pub(in super::super::super) const SELF_MASK: SelfRepr = #self_mask;
                        pub const VALUE_BITS: core::ops::Range<u32> = #value_bits;
                        pub const VALUE_BITS_LEN: usize = (VALUE_BITS.end - VALUE_BITS.start) as usize;
                        pub(in super::super::super) const VALUE_MASK: ValueRepr = #value_mask;

                        pub(in super::super::super) #constness fn self_repr #impl_generics(this: &#strukt_name #ty_generics) -> SelfRepr #where_clause {
                            #assertions
                            #self_repr
                        }

                        pub(in super::super::super) #constness fn self_repr_mut #impl_generics(this: &mut #strukt_name #ty_generics) -> &mut SelfRepr #where_clause {
                            &mut #self_repr
                        }
                    }
                });
            }

            let value_into_from_repr = match use_const {
                false => quote! {
                    pub(in super::super) fn value_into_repr(value: #value_ty) -> #value_repr_ty {
                        <#value_ty as bitbash::ConvertRepr>::into_repr(value)
                    }
                    pub(in super::super) fn value_from_repr(value_repr: #value_repr_ty) -> #value_ty {
                        <#value_ty as bitbash::ConvertRepr>::try_from_repr(value_repr).expect("invalid representation for value")
                    }
                },
                true => match value_ty {
                    Type::Path(p) if is_uint(&p.path) => quote! {
                        pub(in super::super) const fn value_into_repr(value: #value_ty) -> #value_repr_ty {
                            value
                        }
                        pub(in super::super) const fn value_from_repr(value_repr: #value_repr_ty) -> #value_ty {
                            value_repr
                        }
                    },
                    Type::Path(p) if p.path.is_ident("bool") => quote! {
                        pub(in super::super) const fn value_into_repr(value: #value_ty) -> #value_repr_ty {
                            value as #value_repr_ty
                        }
                        pub(in super::super) const fn value_from_repr(value_repr: #value_repr_ty) -> #value_ty {
                            match value_repr {
                                0 => false,
                                1 => true,
                                _ => panic!("invalid representation for value"),
                            }
                        }
                    },
                    value_ty => quote! {
                        pub(in super::super) const fn value_into_repr(value: #value_ty) -> #value_repr_ty {
                            <#value_ty>::const_into_repr(value)
                        }
                        pub(in super::super) const fn value_from_repr(value_repr: #value_repr_ty) -> #value_ty {
                            match <#value_ty>::const_try_from_repr(value_repr) {
                                Some(value) => value,
                                None => panic!("invalid representation for value"),
                            }
                        }
                    },
                },
            };

            let rels = field_rels(field);
            let field_name = &field.name;
            fields_tokens.extend(quote! {
                #[allow(non_snake_case)]
                pub mod #field_name {
                    use super::*;

                    pub(in super::super) type Value = #value_ty;
                    pub(in super::super) type ValueRepr = #value_repr_ty;

                    #value_into_from_repr

                    #rels_tokens

                    pub(in super::super) const VALUE_REPR_MASK: #value_repr_ty = 0 #(| #rels::VALUE_MASK)*;
                }
            });
        }

        let mod_name = format_ident!("__bitfield_{}", strukt.ident);
        tokens.extend(quote! {
            #strukt

            #[allow(non_snake_case)]
            pub mod #mod_name {
                use super::*;
                #fields_tokens
            }
        });

        if let Some(new) = new {
            let mut disable_check = false;
            for attr in &new.attrs {
                match attr {
                    NewAttribute::DisableCheck => disable_check = true,
                }
            }

            let all_field_names: Vec<_> = fields.iter().map(|f| f.name.clone()).collect();
            let new_f = NewF {
                disable_check,
                vis: &new.vis,
                constness: &constness,
                strukt,
                all_field_names: &all_field_names,
                init_field_names: &new.init_field_names,
                init_field_tys: &new.init_field_tys,
            };
            tokens.extend(quote! {
                impl #impl_generics #strukt_name #ty_generics #where_clause {
                    #new_f
                }
            });
        }

        for field in fields {
            let value_ty = &field.value_ty;
            let rels = field_rels(field);

            let mut ro = false;
            let mut private_write = false;
            for attr in &field.attrs {
                match attr {
                    FieldAttribute::ReadOnly => ro = true,
                    FieldAttribute::PrivateWrite => private_write = true,
                }
            }
            let emit_setter = !ro || private_write;

            let field_name = &field.name;
            let field_mod: Path = parse_quote! { #mod_name::#field_name };

            let get_name = field.name.clone();
            let get = Get {
                vis: &field.vis,
                constness: &constness,
                get_name,
                value_ty,
                field_mod: &field_mod,
                rel: &*rels,
            };
            let set = match emit_setter {
                false => None,
                true => Some(Set {
                    vis: match private_write {
                        false => &field.vis,
                        true => &Visibility::Inherited,
                    },
                    constness: &constness,
                    field_name: &field.name,
                    set_name: format_ident!("set_{}", field.name),
                    with_name: format_ident!("with_{}", field.name),
                    value_ty,
                    field_mod: &field_mod,
                    rel: &*rels,
                }),
            };

            tokens.extend(quote! {
                impl #impl_generics #strukt_name #ty_generics #where_clause {
                    #get
                    #set
                }
            });
        }
    }
}

pub struct Get<'a> {
    vis: &'a Visibility,
    constness: &'a Option<Token![const]>,
    get_name: Ident,
    value_ty: &'a Type,
    field_mod: &'a Path,
    rel: &'a [Ident],
}

impl<'a> ToTokens for Get<'a> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let Get {
            vis,
            constness,
            get_name,
            value_ty,
            field_mod,
            rel,
        } = self;
        tokens.extend(quote! {
            #vis #constness fn #get_name(&self) -> #value_ty {
                let mut value_repr: #field_mod::ValueRepr = 0;
                #(value_repr |= (((#field_mod::#rel::self_repr(self) & #field_mod::#rel::SELF_MASK) >> #field_mod::#rel::SELF_BITS.start) as #field_mod::ValueRepr) << #field_mod::#rel::VALUE_BITS.start;)*
                #field_mod::value_from_repr(value_repr)
            }
        });
    }
}

pub struct Set<'a> {
    vis: &'a Visibility,
    constness: &'a Option<Token![const]>,
    field_name: &'a Ident,
    set_name: Ident,
    with_name: Ident,
    value_ty: &'a Type,
    field_mod: &'a Path,
    rel: &'a [Ident],
}

impl<'a> ToTokens for Set<'a> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let Set {
            vis,
            constness,
            field_name,
            set_name,
            with_name,
            value_ty,
            field_mod,
            rel,
        } = self;
        tokens.extend(quote! {
            #vis #constness fn #set_name(&mut self, value: #value_ty) {
                let value_repr: #field_mod::ValueRepr = #field_mod::value_into_repr(value);
                assert!((value_repr & !#field_mod::VALUE_REPR_MASK) == 0, concat!("invalid value for ", stringify!(#field_name)));
                #(*#field_mod::#rel::self_repr_mut(self) =
                    (#field_mod::#rel::self_repr(self) & !#field_mod::#rel::SELF_MASK)
                  | ((((value_repr & #field_mod::#rel::VALUE_MASK) >> #field_mod::#rel::VALUE_BITS.start) as #field_mod::#rel::SelfRepr) << #field_mod::#rel::SELF_BITS.start);
                )*
            }

            #vis #constness fn #with_name(mut self, value: #value_ty) -> Self {
                self.#set_name(value);
                self
            }
        });
    }
}

pub struct NewF<'a> {
    disable_check: bool,
    vis: &'a Visibility,
    constness: &'a Option<Token![const]>,
    strukt: &'a ItemStruct,
    all_field_names: &'a [Ident],
    init_field_names: &'a [Ident],
    init_field_tys: &'a [Type],
}

impl<'a> ToTokens for NewF<'a> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let NewF {
            disable_check,
            vis,
            constness,
            strukt,
            all_field_names,
            init_field_names,
            init_field_tys,
        } = self;

        let strukt_name = &strukt.ident;
        let (_, ty_generics, _) = strukt.generics.split_for_impl();

        let with_init_field = init_field_names
            .iter()
            .map(|name| format_ident!("with_{}", name));

        fn initializer(ty: &Type) -> Expr {
            match ty {
                Type::Array(t) => {
                    let len = &t.len;
                    parse_quote! { [0; #len] }
                }
                _ => parse_quote! { 0 },
            }
        }
        let zero_initializer = match &strukt.fields {
            Fields::Unnamed(fields) => {
                let initializer = initializer(&fields.unnamed[0].ty);
                quote! { #strukt_name(#initializer) }
            }
            Fields::Named(fields) => {
                let field_name = fields.named.iter().map(|f| &f.ident);
                let initializer = fields.named.iter().map(|f| initializer(&f.ty));
                quote! { #strukt_name {
                    #(#field_name: #initializer,)*
                }}
            }
            Fields::Unit => unreachable!(),
        };
        let check = match disable_check {
            true => None,
            false => Some(quote! { #(let _ = this.#all_field_names();)* }),
        };
        tokens.extend(quote! {
            #vis #constness fn new(#(#init_field_names: #init_field_tys),*) -> #strukt_name #ty_generics {
                let this = #zero_initializer #(.#with_init_field(#init_field_names))*;
                #check
                this
            }
        })
    }
}
