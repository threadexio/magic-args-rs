//! "Magic" declarative-style function arguments.
//!
//! A cursed exercise of the type system.
//!
//! ```
//! # use magic_args::apply;
//! fn f0() { /* ... */ }
//! fn f1(x: i32) { /* ... */ }
//! fn f2(x: i32, z: usize) { /* ... */ }
//! async fn f3(y: &'static str) { /* ... */ }
//! async fn f4(y: &'static str, x: i32, z: usize) { /* ... */ }
//!
//! let args = (-42_i32, "🦀", 42_usize);
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
//! ```
//! use magic_args::apply;
//!
//! fn f(x: usize, z: &str) -> usize { x + z.len() }
//!
//! let args = (31_i32, "foo", 42_usize);
//!
//! let y = apply(f, args);
//! assert_eq!(y, 45);
//! ```
//!
//! It is also possible to have a custom type as `args` (instead of a tuple).
//!
//! ```
//! use magic_args::{apply, MagicArgs};
//!
//! fn f(x: usize, z: &str) -> usize { x + z.len() }
//!
//! #[derive(MagicArgs)]
//! struct MyArgs(i32, &'static str, usize);
//!
//! let args = MyArgs(31, "foo", 42);
//!
//! let y = apply(f, args);
//! assert_eq!(y, 45);
//! ```
//!
//! # How it works
//!
//! The core of this crate is [`Callable`] and [`Args`]. Everything else is only
//! for convenience and ease of use.
//!
//! I will now try to _briefly_ explain how this crate works.
//!
//! ## The [`Args`] trait
//!
//! The [`Args`] trait describes any kind of type that can act as an "argument
//! set". This is essentially the type which contains every argument available.
//!
//! The [`Args`] trait has blanket implementations for tuples of up to 32
//! elements. It is also possible to turn any type into [`Args`] with the
//! [`macro@MagicArgs`] macro. It _is_ possible to hand-implement [`Args`] but
//! this is not recommended as you must rely on the internal constructs of this
//! crate that are subject to change at any time.
//!
//! ## The [`Callable`] trait
//!
//! This is where the magic happens. [`Callable`] describes anything that can
//! be called with an argument set. It is blanket-implemented for any `FnOnce`
//! with up to 32 arguments.
//!
//! The trait is defined over $A$ and $T$. $A$ is the argument set needed and
//! $T$ is an ordered tuple which contains the types of the arguments the
//! function expects to receive. For example, in the following function:
//!
//! ```no_run
//! fn f(x: u32, y: i32, z: usize) {}
//! ```
//!
//! $A$ is any `A: Args<u32> + Args<i32> + Args<usize>` and $T$ is `(u32, i32,
//! usize)`. The type parameter $T$ is only there to provide disambiguation
//! for the different `impl`s. Without it, it would be impossible to provide
//! implementations of `Callable<A>` for `FnOnce()` and `FnOnce(U)` at the same
//! time. This is because the language, at this time, lacks [specialized trait
//! `impl`s]. With $T$, the implemented trait is `Callable<A, ()>` for `FnOnce()`
//! and `Callable<A, (U,)>` for `FnOnce(U)` (which are technically different
//! traits and thus are allowed to coexist with blanket implementations).
//!
//! ## An implementation detail
//!
//! **NOTE:** This section serves only as a guide for hackers and just
//! to explain how the crate works. Nothing here is to be considered as a
//! semver-stable API. Consider yourself warned.
//!
//! If you tried to implement [`Args`] for a tuple of `(T0, T1)`, it would
//! probably look a bit like this:
//!
//! ```compile_fail,E0119
//! # use magic_args::Args;
//! impl<T0: Clone, T1> Args<T0> for (T0, T1) {
//!     fn get(&self) -> T0 { self.0.clone() }
//! }
//!
//! impl<T0, T1: Clone> Args<T1> for (T0, T1) {
//!     fn get(&self) -> T1 { self.1.clone() }
//! }
//! ```
//!
//! Which, as you might have guessed from the red border above, does not work.
//! This is because the above implementations are not well-defined. Consider the
//! following type, $(i32, i32)$. What happens when we invoke [`Args::get`] on
//! that type? Do we get back the first or the second field? This is the edge
//! case the compiler tries to warn us about. As of writing this crate, there is
//! no support for specifying type bounds like `T0 != T1`. So we can't just say
//! "where `T0 != T1`" and be done.
//!
//! There is another, arguably more convuluted way to describe this. If we
//! introduce a type `Tagged<T, const N: usize>(T)` we can have many "unique"
//! $T$s. This is because `Tagged<i32, 0>` is not the same as `Tagged<i32, 1>`.
//! We can use this little property to modify our [`Args`] implementation a bit;
//! instead of returning `T0` or `T1`, we return `Tagged<T0, 0>` and
//! `Tagged<T1, 1>` respectively. This solves our previous issue of
//! "conflicting implementations" since we are now implementing what is now
//! 2 different traits; `Args<Tagged<T0, 0>>` and `Args<Tagged<T1, 1>>`. We can
//! now modify the [`Callable`] `impl`s to take `const N0: usize`,
//! `const N1: usize` and `A: Args<Tagged<T0, N0>> + Args<Tagged<T1, N1>>`.
//! This solves our issue and allows all implementations to coexist. For tuples,
//! the `N` constant in `Tagged` is the index of the field. The
//! [`macro@MagicArgs`] also uses the index of the field for `N`. `N` is there
//! to serve as a "tag" for each field. Its value does not really matter, only
//! that it is different for each field.
//!
//! # Limitations
//!
//! - This crate operates wholly at the type-level. There is no runtime code
//!   generated as part of resolving arguments, etc. This makes the crate very
//!   difficult to use in a dynamic setting.
//!
//! - You cannot have 2 different instances of the same type as arguments. For
//!   example:
//!
//! ```compile_fail,E0284
//! # use magic_args::apply;
//! fn f(x: i32, y: i32) -> i32 { x + y }
//!
//! let args: (i32, i32) = (42, 31);
//! let _y: i32 = apply(f, args);
//! ```
//!
//!   This can be explained with the following example. Consider the following
//!   function:
//!
//! ```
//! fn f(x: i32, _y: i32) -> i32 { x }
//! ```
//!
//!   Given only the signature of the function, $f: (i32, i32) \to i32$, can you
//!   figure out the correct order to pass the values $42$ and $31$ such that
//!   $f$ returns $42$? Spoiler alert: No. It is impossible. In this case, it is
//!   not clear how we should pass the arguments to the function. Trying the
//!   above will result in a cryptic error message(s). This can be alleviated
//!   however by using a thin wrapper type which semantically conveys the
//!   meaning of the data.
//!
//! ```
//! # use magic_args::apply;
//! #[derive(Clone)]
//! struct X(pub i32);
//!
//! #[derive(Clone)]
//! struct Y(pub i32);
//!
//! fn f(X(x): X, Y(y): Y) -> i32 { x + y }
//!
//! let args = (X(42), Y(31));
//! let y = apply(f, args);
//! assert_eq!(y, 73);
//! ```
//!
//! - Passing non-[`Clone`] arguments is not ideal. Arguments need to be
//!   [`Clone`] so the following is well-defined:
//!
//! ```
//! # use magic_args::apply;
//! fn f(x: i32, y: i32) -> i32 { x + y }
//!
//! let args = (42,);
//! let y = apply(f, args);
//! assert_eq!(y, 84)
//! ```
//!
//!   Notice how this is different than the example before; we are only passing
//!   one [`i32`], not two so there is no ambiguity here. In this case, the
//!   value of [`i32`] is [`Clone::clone`]d and passed both as `x` and as `y`.
//!   Meaning `f` could be rewritten as:
//!
//! ```
//! fn f(x: i32) -> i32 { x * 2 }
//! ```
//!
//!   It is possible to pass non-[`Clone`] arguments, but that needs runtime
//!   checking to ensure only one instance exists. This can be done with
//!   [`std::cell::RefCell`] if necessary.
//!
//! ---
//!
//! Enjoy responsibly!
//!
//! [specialized trait `impl`s]: https://github.com/rust-lang/rust/issues/31844
//! [axum's route handlers]: https://docs.rs/axum/latest/axum/handler/index.html
//! [`std::cell::RefCell`]: https://doc.rust-lang.org/stable/std/cell/struct.RefCell.html

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
    ///
    /// # Examples
    ///
    /// ```
    /// # use magic_args::{apply, MagicArgs};
    /// fn f(x: i32) -> i32 { x + 1 }
    ///
    /// let y = ("🦀", 41).apply(f);
    /// assert_eq!(y, 42);
    /// ```
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
/// fn f(x: i32) -> i32 { x + 1 }
///
/// let y = apply(f, ("🦀", 41));
/// assert_eq!(y, 42);
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
