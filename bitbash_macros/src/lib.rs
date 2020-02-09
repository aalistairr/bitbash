extern crate proc_macro;
use proc_macro::TokenStream;
use proc_macro2::Span;
use syn::Token;

mod bitenum;
mod bitfield;

fn constness(use_const: bool) -> Option<Token![const]> {
    match use_const {
        true => Some(Token![const](Span::call_site())),
        false => None,
    }
}

#[proc_macro_derive(BitEnumConst)]
pub fn bitenum_const(input: TokenStream) -> TokenStream {
    bitenum::bitenum(input, true)
}

#[proc_macro_derive(BitEnumNonConst)]
pub fn bitenum_nonconst(input: TokenStream) -> TokenStream {
    bitenum::bitenum(input, false)
}

#[proc_macro]
pub fn bitfield_const(input: TokenStream) -> TokenStream {
    bitfield::bitfield(input, true)
}

#[proc_macro]
pub fn bitfield_nonconst(input: TokenStream) -> TokenStream {
    bitfield::bitfield(input, false)
}
