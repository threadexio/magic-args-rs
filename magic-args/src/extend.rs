/// Extend a type by another type `T`.
///
/// This trait is mainly used for extending tuples but you can implement it for
/// whatever you like.
pub trait Extend<T> {
    #[expect(missing_docs)]
    type Output;

    #[expect(missing_docs)]
    fn extend(self, item: T) -> Self::Output;
}

///////////////////////////////////////////////////////////////////////////////

macro_rules! impl_extend_tuple {
    ($($T:ident),*) => {
        impl<$($T,)* U> Extend<U> for ($($T,)*) {
            type Output = ($($T,)* U,);

            #[allow(non_snake_case)]
            fn extend(self, item: U) -> Self::Output {
                let ($($T,)*) = self;
                ($($T,)* item,)
            }
        }
    };
}

impl_extend_tuple! {}
impl_extend_tuple! { T0 }
impl_extend_tuple! { T0, T1 }
impl_extend_tuple! { T0, T1, T2 }
impl_extend_tuple! { T0, T1, T2, T3 }
impl_extend_tuple! { T0, T1, T2, T3, T4 }
impl_extend_tuple! { T0, T1, T2, T3, T4, T5 }
impl_extend_tuple! { T0, T1, T2, T3, T4, T5, T6 }
impl_extend_tuple! { T0, T1, T2, T3, T4, T5, T6, T7 }
impl_extend_tuple! { T0, T1, T2, T3, T4, T5, T6, T7, T8 }
impl_extend_tuple! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9 }
impl_extend_tuple! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10 }
impl_extend_tuple! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11 }
impl_extend_tuple! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12 }
impl_extend_tuple! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13 }
impl_extend_tuple! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14 }
impl_extend_tuple! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15 }
impl_extend_tuple! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16 }
impl_extend_tuple! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17 }
impl_extend_tuple! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18 }
impl_extend_tuple! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19 }
impl_extend_tuple! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20 }
impl_extend_tuple! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21 }
impl_extend_tuple! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22 }
impl_extend_tuple! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, T23 }
impl_extend_tuple! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, T23, T24 }
impl_extend_tuple! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, T23, T24, T25 }
impl_extend_tuple! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, T23, T24, T25, T26 }
impl_extend_tuple! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, T23, T24, T25, T26, T27 }
impl_extend_tuple! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, T23, T24, T25, T26, T27, T28 }
impl_extend_tuple! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, T23, T24, T25, T26, T27, T28, T29 }
impl_extend_tuple! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, T23, T24, T25, T26, T27, T28, T29, T30 }
impl_extend_tuple! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, T23, T24, T25, T26, T27, T28, T29, T30, T31 }

///////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_ty<T>(_: T) {}

    #[test]
    fn test_extend_empty() {
        let args = ();
        assert_ty::<(i32,)>(args.extend(1));
    }

    #[test]
    fn test_extend() {
        let args = (1, 2, 3);
        assert_ty::<(i32, i32, i32, i32)>(args.extend(4));
    }
}
