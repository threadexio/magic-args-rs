//! "Magic" declarative-style function arguments.
//!
//! ```
//! # use magic_args::{apply, MagicArgs};
//! fn f0() { /* ... */ }
//! fn f1(x: i32) { /* ... */ }
//! fn f2(x: i32, z: usize) { /* ... */ }
//! async fn f3(y: &'static str) { /* ... */ }
//! async fn f4(y: &'static str, x: i32, z: usize) { /* ... */ }
//!
//! #[derive(MagicArgs)]
//! struct Args(i32, &'static str, usize);
//!
//! let args = Args(-42, "🦀", 42);
//!
//! let _ = apply(f0, &args);
//! let _ = apply(f1, &args);
//! let _ = apply(f2, &args);
//! let _ = apply(f3, &args);
//! let _ = apply(f4, &args);
//! ```
//!
//! The original idea for this crate comes from [axum's route handlers], which
//! do this exact thing with their arguments.
//!
//! # Quick start
//!
//! 1. You define a "set of arguments".
//!
//! ```no_run
//! # use magic_args::MagicArgs;
//! #[derive(MagicArgs)]
//! pub struct MyArgs(&'static str, usize /*, ... */);
//!
//! let args = MyArgs("Hello, world!", 42);
//! ```
//!
//! 2. You use [`apply`] to call a function of your choosing.
//!
//! ```no_run
//! # use magic_args::{apply, MagicArgs};
//! # #[derive(MagicArgs)]
//! # pub struct MyArgs(&'static str, usize /*, ... */);
//! # let args = MyArgs("Hello, world!", 42);
//! fn my_func(msg: &'static str) { /* ... */ }
//!
//! let result = apply(my_func, args);
//! ```
//!
//! 3. Profit? 💰
//!
//!
//!
//! <sub>*this product contains limitations which are not featured above</sub>
//!
//! # How it works
//!
//! All of the "magic" of this crate is done via [`Callable`] and [`Args`].
//! Everything else is purely cosmetic and for convinience.
//!
//! This documentation will use the term "argument set" to refer to any type $T$
//! which implements `Args<U>` for some $U$.
//!
//! [`Callable`] is defined in terms of $A$ and $T$. $A$ is the argument set
//! which contains all arguments available to the function. $T$ is an ordered
//! tuple containing the arguments the function expects to be given.
//! [`Callable`] is implemented automatically for all `FnOnce(T0, T1, ...) -> O`
//! (up to 32 arguments). The job of the [`Callable`] trait is to pick out what
//! arguments the function wants from a given $A$. For this to be possible, $A$
//! must be bounded such that $T \subseteq A$. In other words; to be able to
//! even call the function with the arguments it expects, we must _have_ the
//! arguments in the first place. For example, let $T = (T_0, T_1, T_2)$. It
//! must be that $T_0, T_1, T_2 \in A$ or, in code,
//! `A: Args<T0> + Args<T1> + Args<T2>`. Picking the correct argument from the
//! argument set $A$ for each argument of the function is done with
//! [`Args::get`] and the compiler's type inference.
//!
//! # Limitations
//!
//! This whole crates operates on the type-level of arguments. For this reason,
//! it is impossible to have a function which accepts 2 different instances of
//! the same type. To see why this is, consider the following function:
//!
//! ```no_run
//! fn f(x: i32, _y: i32) -> i32 { x }
//! ```
//!
//! Given its signature $f: (i32, i32) \to i32$ and an arguments set
//! $A = \\{ 42, -42 \\}$. It is impossible to know the correct order of passing
//! these values to $f$ such that it returns 42, or -42 for that matter.
//! This means all values in the argument set must be of a different type. In
//! cases like above when a function has 2 arguments of the same type, the
//! value of the matching type in the argument set is passed twice. This incurs
//! a [`Clone::clone`] call.
//!
//! [axum's route handlers]: https://docs.rs/axum/latest/axum/handler/index.html

#![cfg_attr(docsrs, feature(doc_auto_cfg))]
#![forbid(unsafe_code)]
#![no_std]
extern crate self as magic_args;

#[cfg(feature = "derive")]
/// A derive macro to help you create argument sets.
///
/// This macro can be used only on `struct` items.
///
/// Generate the appropriate [`Args`] implementations for the annotated type
/// allowing it to be used with [`Callable`].
///
/// # Field attributes
///
/// ## `skip`
///
/// * **Syntax:** `#[magic_args(skip)]`
///
/// Do not expose this field as an available argument. The resulting argument
/// set will act as if this field does not exist.
///
/// ```compile_fail,E0277
/// # use magic_args::{apply, MagicArgs};
/// #[derive(MagicArgs)]
/// struct Args(i32, usize, #[magic_args(skip)] &'static str);
///
/// fn f(_x: usize, _y: &'static str) {}
///
/// apply(f, Args(42, 42, "Hello, world!"));
/// ```
#[doc(inline)]
pub use magic_args_derive::MagicArgs;

///////////////////////////////////////////////////////////////////////////////

/// A "set of arguments" that contains `T`.
pub trait Args<T> {
    /// Get `T` from the set of arguments.
    ///
    /// The signature of this method usually means that some copying/cloning
    /// has to happen. To see why it is designed like this, please refer to the
    /// [crate-level documentation](crate).
    fn get(&self) -> T;
}

impl<T, U> Args<T> for &U
where
    U: Args<T>,
{
    fn get(&self) -> T {
        U::get(*self)
    }
}

#[doc(hidden)]
pub mod __private {
    #[derive(Clone)]
    pub struct Tagged<T, const N: usize>(pub T);
}

use self::__private::*;

macro_rules! impl_args_tuple {
    ($($idx:tt: $t:ident),*) => {
        impl_args_tuple!(@impl [$($idx: $t),*]: $(($idx, $t))*);
    };
    (@impl [$($_idx:tt: $_t:ident),*]:) => {};
    (@impl [$($_idx:tt: $_t:ident),*]: ($idx:tt, $t:ident) $($tail:tt)*) => {
        impl<$($_t,)*> Args<Tagged<$t, $idx>> for ($($_t,)*)
        where
            $t: Clone
        {
            fn get(&self) -> Tagged<$t, $idx> {
                Tagged(self.$idx.clone())
            }
        }

        impl_args_tuple!(@impl [$($_idx: $_t),*]: $($tail)*);
    };
}

impl_args_tuple! {}
impl_args_tuple! { 0: T0 }
impl_args_tuple! { 0: T0, 1: T1 }
impl_args_tuple! { 0: T0, 1: T1, 2: T2 }
impl_args_tuple! { 0: T0, 1: T1, 2: T2, 3: T3 }
impl_args_tuple! { 0: T0, 1: T1, 2: T2, 3: T3, 4: T4 }
impl_args_tuple! { 0: T0, 1: T1, 2: T2, 3: T3, 4: T4, 5: T5 }
impl_args_tuple! { 0: T0, 1: T1, 2: T2, 3: T3, 4: T4, 5: T5, 6: T6 }
impl_args_tuple! { 0: T0, 1: T1, 2: T2, 3: T3, 4: T4, 5: T5, 6: T6, 7: T7 }
impl_args_tuple! { 0: T0, 1: T1, 2: T2, 3: T3, 4: T4, 5: T5, 6: T6, 7: T7, 8: T8 }
impl_args_tuple! { 0: T0, 1: T1, 2: T2, 3: T3, 4: T4, 5: T5, 6: T6, 7: T7, 8: T8, 9: T9 }
impl_args_tuple! { 0: T0, 1: T1, 2: T2, 3: T3, 4: T4, 5: T5, 6: T6, 7: T7, 8: T8, 9: T9, 10: T10 }
impl_args_tuple! { 0: T0, 1: T1, 2: T2, 3: T3, 4: T4, 5: T5, 6: T6, 7: T7, 8: T8, 9: T9, 10: T10, 11: T11 }
impl_args_tuple! { 0: T0, 1: T1, 2: T2, 3: T3, 4: T4, 5: T5, 6: T6, 7: T7, 8: T8, 9: T9, 10: T10, 11: T11, 12: T12 }
impl_args_tuple! { 0: T0, 1: T1, 2: T2, 3: T3, 4: T4, 5: T5, 6: T6, 7: T7, 8: T8, 9: T9, 10: T10, 11: T11, 12: T12, 13: T13 }
impl_args_tuple! { 0: T0, 1: T1, 2: T2, 3: T3, 4: T4, 5: T5, 6: T6, 7: T7, 8: T8, 9: T9, 10: T10, 11: T11, 12: T12, 13: T13, 14: T14 }
impl_args_tuple! { 0: T0, 1: T1, 2: T2, 3: T3, 4: T4, 5: T5, 6: T6, 7: T7, 8: T8, 9: T9, 10: T10, 11: T11, 12: T12, 13: T13, 14: T14, 15: T15 }
impl_args_tuple! { 0: T0, 1: T1, 2: T2, 3: T3, 4: T4, 5: T5, 6: T6, 7: T7, 8: T8, 9: T9, 10: T10, 11: T11, 12: T12, 13: T13, 14: T14, 15: T15, 16: T16 }
impl_args_tuple! { 0: T0, 1: T1, 2: T2, 3: T3, 4: T4, 5: T5, 6: T6, 7: T7, 8: T8, 9: T9, 10: T10, 11: T11, 12: T12, 13: T13, 14: T14, 15: T15, 16: T16, 17: T17 }
impl_args_tuple! { 0: T0, 1: T1, 2: T2, 3: T3, 4: T4, 5: T5, 6: T6, 7: T7, 8: T8, 9: T9, 10: T10, 11: T11, 12: T12, 13: T13, 14: T14, 15: T15, 16: T16, 17: T17, 18: T18 }
impl_args_tuple! { 0: T0, 1: T1, 2: T2, 3: T3, 4: T4, 5: T5, 6: T6, 7: T7, 8: T8, 9: T9, 10: T10, 11: T11, 12: T12, 13: T13, 14: T14, 15: T15, 16: T16, 17: T17, 18: T18, 19: T19 }
impl_args_tuple! { 0: T0, 1: T1, 2: T2, 3: T3, 4: T4, 5: T5, 6: T6, 7: T7, 8: T8, 9: T9, 10: T10, 11: T11, 12: T12, 13: T13, 14: T14, 15: T15, 16: T16, 17: T17, 18: T18, 19: T19, 20: T20 }
impl_args_tuple! { 0: T0, 1: T1, 2: T2, 3: T3, 4: T4, 5: T5, 6: T6, 7: T7, 8: T8, 9: T9, 10: T10, 11: T11, 12: T12, 13: T13, 14: T14, 15: T15, 16: T16, 17: T17, 18: T18, 19: T19, 20: T20, 21: T21 }
impl_args_tuple! { 0: T0, 1: T1, 2: T2, 3: T3, 4: T4, 5: T5, 6: T6, 7: T7, 8: T8, 9: T9, 10: T10, 11: T11, 12: T12, 13: T13, 14: T14, 15: T15, 16: T16, 17: T17, 18: T18, 19: T19, 20: T20, 21: T21, 22: T22 }
impl_args_tuple! { 0: T0, 1: T1, 2: T2, 3: T3, 4: T4, 5: T5, 6: T6, 7: T7, 8: T8, 9: T9, 10: T10, 11: T11, 12: T12, 13: T13, 14: T14, 15: T15, 16: T16, 17: T17, 18: T18, 19: T19, 20: T20, 21: T21, 22: T22, 23: T23 }
impl_args_tuple! { 0: T0, 1: T1, 2: T2, 3: T3, 4: T4, 5: T5, 6: T6, 7: T7, 8: T8, 9: T9, 10: T10, 11: T11, 12: T12, 13: T13, 14: T14, 15: T15, 16: T16, 17: T17, 18: T18, 19: T19, 20: T20, 21: T21, 22: T22, 23: T23, 24: T24 }
impl_args_tuple! { 0: T0, 1: T1, 2: T2, 3: T3, 4: T4, 5: T5, 6: T6, 7: T7, 8: T8, 9: T9, 10: T10, 11: T11, 12: T12, 13: T13, 14: T14, 15: T15, 16: T16, 17: T17, 18: T18, 19: T19, 20: T20, 21: T21, 22: T22, 23: T23, 24: T24, 25: T25 }
impl_args_tuple! { 0: T0, 1: T1, 2: T2, 3: T3, 4: T4, 5: T5, 6: T6, 7: T7, 8: T8, 9: T9, 10: T10, 11: T11, 12: T12, 13: T13, 14: T14, 15: T15, 16: T16, 17: T17, 18: T18, 19: T19, 20: T20, 21: T21, 22: T22, 23: T23, 24: T24, 25: T25, 26: T26 }
impl_args_tuple! { 0: T0, 1: T1, 2: T2, 3: T3, 4: T4, 5: T5, 6: T6, 7: T7, 8: T8, 9: T9, 10: T10, 11: T11, 12: T12, 13: T13, 14: T14, 15: T15, 16: T16, 17: T17, 18: T18, 19: T19, 20: T20, 21: T21, 22: T22, 23: T23, 24: T24, 25: T25, 26: T26, 27: T27 }
impl_args_tuple! { 0: T0, 1: T1, 2: T2, 3: T3, 4: T4, 5: T5, 6: T6, 7: T7, 8: T8, 9: T9, 10: T10, 11: T11, 12: T12, 13: T13, 14: T14, 15: T15, 16: T16, 17: T17, 18: T18, 19: T19, 20: T20, 21: T21, 22: T22, 23: T23, 24: T24, 25: T25, 26: T26, 27: T27, 28: T28 }
impl_args_tuple! { 0: T0, 1: T1, 2: T2, 3: T3, 4: T4, 5: T5, 6: T6, 7: T7, 8: T8, 9: T9, 10: T10, 11: T11, 12: T12, 13: T13, 14: T14, 15: T15, 16: T16, 17: T17, 18: T18, 19: T19, 20: T20, 21: T21, 22: T22, 23: T23, 24: T24, 25: T25, 26: T26, 27: T27, 28: T28, 29: T29 }
impl_args_tuple! { 0: T0, 1: T1, 2: T2, 3: T3, 4: T4, 5: T5, 6: T6, 7: T7, 8: T8, 9: T9, 10: T10, 11: T11, 12: T12, 13: T13, 14: T14, 15: T15, 16: T16, 17: T17, 18: T18, 19: T19, 20: T20, 21: T21, 22: T22, 23: T23, 24: T24, 25: T25, 26: T26, 27: T27, 28: T28, 29: T29, 30: T30 }
impl_args_tuple! { 0: T0, 1: T1, 2: T2, 3: T3, 4: T4, 5: T5, 6: T6, 7: T7, 8: T8, 9: T9, 10: T10, 11: T11, 12: T12, 13: T13, 14: T14, 15: T15, 16: T16, 17: T17, 18: T18, 19: T19, 20: T20, 21: T21, 22: T22, 23: T23, 24: T24, 25: T25, 26: T26, 27: T27, 28: T28, 29: T29, 30: T30, 31: T31 }

///////////////////////////////////////////////////////////////////////////////

/// A trait to describe any kind of type that can be called.
///
/// This trait and the [`Args`] trait are the foundation of the crate. It
/// provides [`Callable::call`] which is how [`apply`] (and friends) work.
pub trait Callable<A, T> {
    type Output;

    fn call(self, args: A) -> Self::Output;
}

macro_rules! impl_callable_fnonce {
    ($($t:ident: $n:ident),*) => {
        impl<F, O, A, $($t,)* $(const $n: usize,)*> Callable<A, ($(Tagged<$t, $n>,)*)> for F
        where
            F: FnOnce($($t),*) -> O,
            $(A: Args<Tagged<$t, $n>>,)*
        {
            type Output = O;

            #[allow(non_snake_case)]
            fn call(self, _args: A) -> Self::Output {
                $(let $t = <A as Args<Tagged<$t, $n>>>::get(&_args);)*
                (self)($($t.0,)*)
            }
        }
    };
}

impl_callable_fnonce! {}
impl_callable_fnonce! { T0: N0 }
impl_callable_fnonce! { T0: N0, T1: N1 }
impl_callable_fnonce! { T0: N0, T1: N1, T2: N2 }
impl_callable_fnonce! { T0: N0, T1: N1, T2: N2, T3: N3 }
impl_callable_fnonce! { T0: N0, T1: N1, T2: N2, T3: N3, T4: N4 }
impl_callable_fnonce! { T0: N0, T1: N1, T2: N2, T3: N3, T4: N4, T5: N5 }
impl_callable_fnonce! { T0: N0, T1: N1, T2: N2, T3: N3, T4: N4, T5: N5, T6: N6 }
impl_callable_fnonce! { T0: N0, T1: N1, T2: N2, T3: N3, T4: N4, T5: N5, T6: N6, T7: N7 }
impl_callable_fnonce! { T0: N0, T1: N1, T2: N2, T3: N3, T4: N4, T5: N5, T6: N6, T7: N7, T8: N8 }
impl_callable_fnonce! { T0: N0, T1: N1, T2: N2, T3: N3, T4: N4, T5: N5, T6: N6, T7: N7, T8: N8, T9: N9 }
impl_callable_fnonce! { T0: N0, T1: N1, T2: N2, T3: N3, T4: N4, T5: N5, T6: N6, T7: N7, T8: N8, T9: N9, T10: N10 }
impl_callable_fnonce! { T0: N0, T1: N1, T2: N2, T3: N3, T4: N4, T5: N5, T6: N6, T7: N7, T8: N8, T9: N9, T10: N10, T11: N11 }
impl_callable_fnonce! { T0: N0, T1: N1, T2: N2, T3: N3, T4: N4, T5: N5, T6: N6, T7: N7, T8: N8, T9: N9, T10: N10, T11: N11, T12: N12 }
impl_callable_fnonce! { T0: N0, T1: N1, T2: N2, T3: N3, T4: N4, T5: N5, T6: N6, T7: N7, T8: N8, T9: N9, T10: N10, T11: N11, T12: N12, T13: N13 }
impl_callable_fnonce! { T0: N0, T1: N1, T2: N2, T3: N3, T4: N4, T5: N5, T6: N6, T7: N7, T8: N8, T9: N9, T10: N10, T11: N11, T12: N12, T13: N13, T14: N14 }
impl_callable_fnonce! { T0: N0, T1: N1, T2: N2, T3: N3, T4: N4, T5: N5, T6: N6, T7: N7, T8: N8, T9: N9, T10: N10, T11: N11, T12: N12, T13: N13, T14: N14, T15: N15 }
impl_callable_fnonce! { T0: N0, T1: N1, T2: N2, T3: N3, T4: N4, T5: N5, T6: N6, T7: N7, T8: N8, T9: N9, T10: N10, T11: N11, T12: N12, T13: N13, T14: N14, T15: N15, T16: N16 }
impl_callable_fnonce! { T0: N0, T1: N1, T2: N2, T3: N3, T4: N4, T5: N5, T6: N6, T7: N7, T8: N8, T9: N9, T10: N10, T11: N11, T12: N12, T13: N13, T14: N14, T15: N15, T16: N16, T17: N17 }
impl_callable_fnonce! { T0: N0, T1: N1, T2: N2, T3: N3, T4: N4, T5: N5, T6: N6, T7: N7, T8: N8, T9: N9, T10: N10, T11: N11, T12: N12, T13: N13, T14: N14, T15: N15, T16: N16, T17: N17, T18: N18 }
impl_callable_fnonce! { T0: N0, T1: N1, T2: N2, T3: N3, T4: N4, T5: N5, T6: N6, T7: N7, T8: N8, T9: N9, T10: N10, T11: N11, T12: N12, T13: N13, T14: N14, T15: N15, T16: N16, T17: N17, T18: N18, T19: N19 }
impl_callable_fnonce! { T0: N0, T1: N1, T2: N2, T3: N3, T4: N4, T5: N5, T6: N6, T7: N7, T8: N8, T9: N9, T10: N10, T11: N11, T12: N12, T13: N13, T14: N14, T15: N15, T16: N16, T17: N17, T18: N18, T19: N19, T20: N20 }
impl_callable_fnonce! { T0: N0, T1: N1, T2: N2, T3: N3, T4: N4, T5: N5, T6: N6, T7: N7, T8: N8, T9: N9, T10: N10, T11: N11, T12: N12, T13: N13, T14: N14, T15: N15, T16: N16, T17: N17, T18: N18, T19: N19, T20: N20, T21: N21 }
impl_callable_fnonce! { T0: N0, T1: N1, T2: N2, T3: N3, T4: N4, T5: N5, T6: N6, T7: N7, T8: N8, T9: N9, T10: N10, T11: N11, T12: N12, T13: N13, T14: N14, T15: N15, T16: N16, T17: N17, T18: N18, T19: N19, T20: N20, T21: N21, T22: N22 }
impl_callable_fnonce! { T0: N0, T1: N1, T2: N2, T3: N3, T4: N4, T5: N5, T6: N6, T7: N7, T8: N8, T9: N9, T10: N10, T11: N11, T12: N12, T13: N13, T14: N14, T15: N15, T16: N16, T17: N17, T18: N18, T19: N19, T20: N20, T21: N21, T22: N22, T23: N23 }
impl_callable_fnonce! { T0: N0, T1: N1, T2: N2, T3: N3, T4: N4, T5: N5, T6: N6, T7: N7, T8: N8, T9: N9, T10: N10, T11: N11, T12: N12, T13: N13, T14: N14, T15: N15, T16: N16, T17: N17, T18: N18, T19: N19, T20: N20, T21: N21, T22: N22, T23: N23, T24: N24 }
impl_callable_fnonce! { T0: N0, T1: N1, T2: N2, T3: N3, T4: N4, T5: N5, T6: N6, T7: N7, T8: N8, T9: N9, T10: N10, T11: N11, T12: N12, T13: N13, T14: N14, T15: N15, T16: N16, T17: N17, T18: N18, T19: N19, T20: N20, T21: N21, T22: N22, T23: N23, T24: N24, T25: N25 }
impl_callable_fnonce! { T0: N0, T1: N1, T2: N2, T3: N3, T4: N4, T5: N5, T6: N6, T7: N7, T8: N8, T9: N9, T10: N10, T11: N11, T12: N12, T13: N13, T14: N14, T15: N15, T16: N16, T17: N17, T18: N18, T19: N19, T20: N20, T21: N21, T22: N22, T23: N23, T24: N24, T25: N25, T26: N26 }
impl_callable_fnonce! { T0: N0, T1: N1, T2: N2, T3: N3, T4: N4, T5: N5, T6: N6, T7: N7, T8: N8, T9: N9, T10: N10, T11: N11, T12: N12, T13: N13, T14: N14, T15: N15, T16: N16, T17: N17, T18: N18, T19: N19, T20: N20, T21: N21, T22: N22, T23: N23, T24: N24, T25: N25, T26: N26, T27: N27 }
impl_callable_fnonce! { T0: N0, T1: N1, T2: N2, T3: N3, T4: N4, T5: N5, T6: N6, T7: N7, T8: N8, T9: N9, T10: N10, T11: N11, T12: N12, T13: N13, T14: N14, T15: N15, T16: N16, T17: N17, T18: N18, T19: N19, T20: N20, T21: N21, T22: N22, T23: N23, T24: N24, T25: N25, T26: N26, T27: N27, T28: N28 }
impl_callable_fnonce! { T0: N0, T1: N1, T2: N2, T3: N3, T4: N4, T5: N5, T6: N6, T7: N7, T8: N8, T9: N9, T10: N10, T11: N11, T12: N12, T13: N13, T14: N14, T15: N15, T16: N16, T17: N17, T18: N18, T19: N19, T20: N20, T21: N21, T22: N22, T23: N23, T24: N24, T25: N25, T26: N26, T27: N27, T28: N28, T29: N29 }
impl_callable_fnonce! { T0: N0, T1: N1, T2: N2, T3: N3, T4: N4, T5: N5, T6: N6, T7: N7, T8: N8, T9: N9, T10: N10, T11: N11, T12: N12, T13: N13, T14: N14, T15: N15, T16: N16, T17: N17, T18: N18, T19: N19, T20: N20, T21: N21, T22: N22, T23: N23, T24: N24, T25: N25, T26: N26, T27: N27, T28: N28, T29: N29, T30: N30 }
impl_callable_fnonce! { T0: N0, T1: N1, T2: N2, T3: N3, T4: N4, T5: N5, T6: N6, T7: N7, T8: N8, T9: N9, T10: N10, T11: N11, T12: N12, T13: N13, T14: N14, T15: N15, T16: N16, T17: N17, T18: N18, T19: N19, T20: N20, T21: N21, T22: N22, T23: N23, T24: N24, T25: N25, T26: N26, T27: N27, T28: N28, T29: N29, T30: N30, T31: N31 }

///////////////////////////////////////////////////////////////////////////////

/// A convinience trait to provide the `args.apply(f)` syntax.
pub trait MagicArgs {
    /// Apply _f_ on `self`.
    ///
    /// Equivalent to: `apply(f, self)`.
    ///
    /// See: [`apply`].
    fn apply<C, T>(self, f: C) -> C::Output
    where
        C: Callable<Self, T>,
        Self: Sized;
}

impl<U> MagicArgs for U {
    #[inline]
    fn apply<C, T>(self, f: C) -> C::Output
    where
        C: Callable<Self, T>,
        Self: Sized,
    {
        apply(f, self)
    }
}

/// Apply _f_ on `args`.
///
/// Equivalent to: `f.call(args)`.
///
/// See: [`Callable::call`].
///
/// # Examples
///
/// ```
/// # use magic_args::{apply, MagicArgs};
/// #[derive(MagicArgs)]
/// struct Args(String, i32);
///
/// fn f(x: i32) -> i32 { x + 1 }
///
/// let args = Args("🦀".into(), 41);
/// let y = apply(f, args);
/// assert_eq!(y, 42);
/// ```
///
/// ---
///
/// ```
/// # use magic_args::{apply, MagicArgs};
/// #[derive(MagicArgs)]
/// struct Args(String, i32);
///
/// let args = Args("🦀".into(), 41);
///
/// let fs: [fn(i32) -> i32; _] = [
///     (|x| x + 1),
///     (|x| x * 2),
///     (|x| 3 * x + 1),
///     (|x| -x),
/// ];
///
/// let results = fs.map(|f| apply(f, &args));
///
/// assert_eq!(results, [
///     42,
///     82,
///     124,
///     -41
/// ]);
/// ```
#[inline]
pub fn apply<C, A, T>(f: C, args: A) -> C::Output
where
    C: Callable<A, T>,
{
    f.call(args)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sync_functions() {
        let args = (42u32, 31i32);

        fn f0() -> i32 {
            42
        }

        fn f1(x: u32) -> i32 {
            x as i32
        }

        fn f2(y: i32, x: u32) -> i32 {
            y + x as i32
        }

        fn f3(x: u32, y: u32) -> u32 {
            x + y
        }

        assert_eq!(args.apply(f0), 42);
        assert_eq!(args.apply(f1), 42);
        assert_eq!(args.apply(f2), 73);
        assert_eq!(args.apply(f3), 84);
    }

    #[test]
    fn test_sync_closures() {
        let args = (42u32, 31i32);

        let data = &[1_i32, 2, 3, 4, 5];

        assert_eq!(args.apply(|| { data.iter().sum::<i32>() }), 15);
        assert_eq!(
            args.apply(|x: u32| { data.iter().sum::<i32>() + x as i32 }),
            57
        );
        assert_eq!(
            args.apply(|y: i32, x: u32| { data.iter().sum::<i32>() + y + x as i32 }),
            88
        );
        assert_eq!(
            args.apply(|x: u32, y: u32| { data.iter().sum::<i32>() as u32 + x + y }),
            99
        );
    }

    #[test]
    fn test_async() {
        fn assert_future<F: Future>(_f: F) {}

        let args = (42u32, 31i32);

        async fn f0() -> i32 {
            42
        }

        async fn f1(x: u32) -> i32 {
            x as i32
        }

        async fn f2(y: i32, x: u32) -> i32 {
            y + x as i32
        }

        async fn f3(x: u32, y: u32) -> u32 {
            x + y
        }

        assert_future(args.apply(f0));
        assert_future(args.apply(f1));
        assert_future(args.apply(f2));
        assert_future(args.apply(f3));
    }

    #[cfg(feature = "derive")]
    mod derive {
        use super::*;

        #[test]
        fn test_derive_tuple() {
            #[derive(MagicArgs)]
            struct MyArgs(i32, u32);

            let args = MyArgs(42, 31);
            assert_eq!(args.apply(|x: u32, _y: i32| x as i32), 31);
        }

        #[test]
        fn test_derive_struct() {
            #[derive(MagicArgs)]
            struct MyArgs {
                x: i32,
                y: u32,
            }

            let args = MyArgs { x: 42, y: 31 };
            assert_eq!(args.apply(|x: u32, _y: i32| x as i32), 31);
        }

        #[test]
        fn test_derive_struct_lifetime() {
            #[derive(MagicArgs)]
            struct MyArgs<'a>(&'a str);

            let args = MyArgs("Hello, World!");
            assert_eq!(args.apply(|x: &str| x.len()), 13);
        }
    }
}
