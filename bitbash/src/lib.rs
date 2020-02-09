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

                new(e);

                field a: bool = [31];
                field b: u8 = [0..8];
                field c: u8 = [8..12] ~ [16..20];
                field d: u32 {
                    [12..16] => [12..16],
                    [20..24] => [20..24],
                }
                field e: FooE = [24..28];
            }

            #[derive(crate::$BitEnum, Copy, Clone, PartialEq, Eq, Debug)]
            enum FooE {
                A = 0b1010,
                B = 0b0101,
            }

            #[test]
            fn foo() {
                let mut foo = Foo::new(FooE::A);
                assert_eq!(foo.a(), false);
                assert_eq!(foo.b(), 0u8);
                assert_eq!(foo.c(), 0u8);
                assert_eq!(foo.d(), 0u32);
                assert_eq!(foo.e(), FooE::A);
                assert_eq!(foo.0, (FooE::A as u32) << 24);
                foo.set_a(true);
                foo.set_b(0x12u8);
                foo.set_c(0x34u8);
                foo.set_d((0x5u32 << 12) | (0x6u32 << 20));
                foo.set_e(FooE::B);
                assert_eq!(foo.a(), true);
                assert_eq!(foo.b(), 0x12u8);
                assert_eq!(foo.c(), 0x34u8);
                assert_eq!(foo.d(), (0x5u32 << 12) | (0x6u32 << 20));
                assert_eq!(foo.e(), FooE::B);
                assert_eq!(
                    foo.0,
                    (1 << 31)
                        | (0x12 << 0)
                        | ((0x4 << 8) | (0x3 << 16))
                        | ((0x5 << 12) | (0x6 << 20))
                        | ((FooE::B as u32) << 24)
                );
            }

            const BAR_LEN: usize = 2;

            $crate::bitfield! {
                struct Bar([u32; BAR_LEN]);

                new();

                field a: u32 = 0;
                field b: u8 = (BAR_LEN - 1)[16..24];
            }

            #[test]
            fn bar() {
                let mut bar = Bar::new();
                assert_eq!(bar.a(), 0);
                assert_eq!(bar.b(), 0);
                assert_eq!(bar.0, [0, 0]);
                bar.set_a(1);
                bar.set_b(2);
                assert_eq!(bar.a(), 1);
                assert_eq!(bar.b(), 2);
                assert_eq!(bar.0, [1, 2 << 16]);
            }

            $crate::bitfield! {
                struct Baz {
                    _padding0: [u32; 1],
                    a0: u32,
                    a1: u32,
                    _padding1: [u32; 2],
                    pub b: u32,
                }

                new();

                field a: u64 = a0 ~ a1;
            }

            #[test]
            fn baz() {
                let mut baz = Baz::new();
                assert_eq!(baz.a(), 0);
                assert_eq!(baz._padding0, [0]);
                assert_eq!(baz.a0, 0);
                assert_eq!(baz.a1, 0);
                assert_eq!(baz._padding1, [0, 0]);
                assert_eq!(baz.b, 0);
                baz.set_a(!0);
                assert_eq!(baz.a(), !0);
                assert_eq!(baz._padding0, [0]);
                assert_eq!(baz.a0, !0);
                assert_eq!(baz.a1, !0);
                assert_eq!(baz._padding1, [0, 0]);
                assert_eq!(baz.b, 0);
                baz.b = 0x10101010;
                assert_eq!(baz.a(), !0);
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
