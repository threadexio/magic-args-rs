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
    ($($t:ident),*) => {
        impl<F, O, A, $($t,)*> Callable<A, ($($t,)*)> for F
        where
            F: FnOnce($($t),*) -> O,
            $(A: Args<$t>,)*
        {
            type Output = O;

            fn call(self, _args: A) -> Self::Output {
                (self)($(<A as Args<$t>>::get(&_args)),*)
            }
        }
    };
}

impl_callable_fnonce! {}
impl_callable_fnonce! { T0 }
impl_callable_fnonce! { T0, T1 }
impl_callable_fnonce! { T0, T1, T2 }
impl_callable_fnonce! { T0, T1, T2, T3 }
impl_callable_fnonce! { T0, T1, T2, T3, T4 }
impl_callable_fnonce! { T0, T1, T2, T3, T4, T5 }
impl_callable_fnonce! { T0, T1, T2, T3, T4, T5, T6 }
impl_callable_fnonce! { T0, T1, T2, T3, T4, T5, T6, T7 }
impl_callable_fnonce! { T0, T1, T2, T3, T4, T5, T6, T7, T8 }
impl_callable_fnonce! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9 }
impl_callable_fnonce! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10 }
impl_callable_fnonce! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11 }
impl_callable_fnonce! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12 }
impl_callable_fnonce! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13 }
impl_callable_fnonce! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14 }
impl_callable_fnonce! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15 }
impl_callable_fnonce! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16 }
impl_callable_fnonce! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17 }
impl_callable_fnonce! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18 }
impl_callable_fnonce! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19 }
impl_callable_fnonce! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20 }
impl_callable_fnonce! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21 }
impl_callable_fnonce! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22 }
impl_callable_fnonce! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, T23 }
impl_callable_fnonce! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, T23, T24 }
impl_callable_fnonce! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, T23, T24, T25 }
impl_callable_fnonce! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, T23, T24, T25, T26 }
impl_callable_fnonce! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, T23, T24, T25, T26, T27 }
impl_callable_fnonce! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, T23, T24, T25, T26, T27, T28 }
impl_callable_fnonce! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, T23, T24, T25, T26, T27, T28, T29 }
impl_callable_fnonce! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, T23, T24, T25, T26, T27, T28, T29, T30 }
impl_callable_fnonce! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, T23, T24, T25, T26, T27, T28, T29, T30, T31 }

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

    #[derive(Clone)]
    struct A;
    #[derive(Clone)]
    struct B;
    #[derive(Clone)]
    struct C;
    #[derive(Clone)]
    struct D;

    #[derive(MagicArgs)]
    struct Args(A, B, C, D);

    const fn args() -> Args {
        Args(A, B, C, D)
    }

    #[test]
    fn test_sync_functions() {
        let args = args();

        fn f0() {}
        fn f1(_a: A) {}
        fn f2(_c: C, _d: D) {}
        fn f3(_a: A, _b: B, _c: C, _d: D) {}

        apply(f0, &args);
        apply(f1, &args);
        apply(f2, &args);
        apply(f3, &args);
    }

    #[test]
    fn test_sync_closures() {
        let args = args();

        let f0 = || {};
        let f1 = |_a: A| {};
        let f2 = |_c: C, _d: D| {};
        let f3 = |_a: A, _b: B, _c: C, _d: D| {};

        apply(f0, &args);
        apply(f1, &args);
        apply(f2, &args);
        apply(f3, &args);
    }

    #[test]
    fn test_async_functions() {
        let args = args();

        async fn f0() {}
        async fn f1(_a: A) {}
        async fn f2(_c: C, _d: D) {}
        async fn f3(_a: A, _b: B, _c: C, _d: D) {}

        drop(apply(f0, &args));
        drop(apply(f1, &args));
        drop(apply(f2, &args));
        drop(apply(f3, &args));
    }

    #[test]
    fn test_async_closures() {
        let args = args();

        let f0 = async || {};
        let f1 = async |_a: A| {};
        let f2 = async |_c: C, _d: D| {};
        let f3 = async |_a: A, _b: B, _c: C, _d: D| {};

        drop(apply(f0, &args));
        drop(apply(f1, &args));
        drop(apply(f2, &args));
        drop(apply(f3, &args));
    }
}
