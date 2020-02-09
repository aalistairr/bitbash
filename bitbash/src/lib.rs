#![cfg_attr(
    all(test, feature = "const"),
    feature(const_fn, const_panic, const_if_match, const_mut_refs)
)]

pub use bitbash_macros::{bitfield_const, bitfield_nonconst, BitEnumConst, BitEnumNonConst};

#[cfg(feature = "const")]
pub use self::{bitfield_const as bitfield, BitEnumConst as BitEnum};
#[cfg(not(feature = "const"))]
pub use self::{bitfield_nonconst as bitfield, BitEnumNonConst as BitEnum};

pub trait ConvertRepr: Sized {
    type Repr;

    fn try_from_repr(repr: Self::Repr) -> Option<Self>;
    fn into_repr(self) -> Self::Repr;
}

macro_rules! impl_convert_repr {
    ($($t:ty),*) => {$(
        impl ConvertRepr for $t {
            type Repr = $t;

            fn try_from_repr(repr: $t) -> Option<$t> {
                Some(repr)
            }

            fn into_repr(self) -> $t {
                self
            }
        }
    )*}
}
impl_convert_repr!(usize, u8, u16, u32, u64, u128);

impl ConvertRepr for bool {
    type Repr = u8;

    fn try_from_repr(repr: u8) -> Option<bool> {
        match repr {
            0 => Some(false),
            1 => Some(true),
            _ => None,
        }
    }

    fn into_repr(self) -> u8 {
        self as u8
    }
}

#[cfg(test)]
mod tests {
    macro_rules! tests {
        ($bitfield:tt, $BitEnum:tt) => {
            #[allow(unused_imports)]
            use crate as bitbash;
            crate::$bitfield! {
                struct Foo(u32);

                field a: bool = [31];
                field b: u8 = [0..8];
                field c: u8 = [8..12] ~ [16..20];
                field d: u32 {
                    [12..16] => [12..16],
                    [20..24] => [20..24],
                }
                field e: Bar = [24..28];
            }

            #[derive(crate::$BitEnum, Copy, Clone, PartialEq, Eq, Debug)]
            enum Bar {
                A = 0b0000,
                B = 0b1010,
            }

            #[test]
            fn foo() {
                let mut foo = Foo(0);
                assert_eq!(foo.a(), false);
                assert_eq!(foo.b(), 0u8);
                assert_eq!(foo.c(), 0u8);
                assert_eq!(foo.d(), 0u32);
                assert_eq!(foo.e(), Bar::A);
                foo.set_a(true);
                foo.set_b(0x12u8);
                foo.set_c(0x34u8);
                foo.set_d((0x5u32 << 12) | (0x6u32 << 20));
                foo.set_e(Bar::B);
                assert_eq!(foo.a(), true);
                assert_eq!(foo.b(), 0x12u8);
                assert_eq!(foo.c(), 0x34u8);
                assert_eq!(foo.d(), (0x5u32 << 12) | (0x6u32 << 20));
                assert_eq!(foo.e(), Bar::B);
                assert_eq!(
                    foo.0,
                    (1 << 31)
                        | (0x12 << 0)
                        | ((0x4 << 8) | (0x3 << 16))
                        | ((0x5 << 12) | (0x6 << 20))
                        | (0b1010 << 24)
                );
            }
        };
    }
    #[cfg(feature = "const")]
    mod konst {
        tests!(bitfield_const, BitEnumConst);
    }
    mod nonconst {
        tests!(bitfield_nonconst, BitEnumNonConst);
    }
}
