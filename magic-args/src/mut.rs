use core::borrow::{Borrow, BorrowMut};
use core::cell::Cell;
use core::ops::{Deref, DerefMut};
use core::ptr::NonNull;

///////////////////////////////////////////////////////////////////////////////

/// A [`Clone`]-once wrapper.
///
/// [`Mut`] allows passing types like `&mut T` safely. [`Mut`] implements a
/// dummy [`Clone`] that allows being cloned exactly once. This allows passing
/// non-[`Clone`] types by moving them between [`Mut`]s. [`Mut`] can be thought
/// of a bit like [`Option`]. [`Mut`] contains a value and when it is [`Clone`]d
/// the value inside is moved to the new [`Mut`] leaving [`None`] in the old
/// [`Mut`]. This approach has the disadvantage that the uniqueness check
/// becomes a runtime panic.
///
/// # Panics
///
/// [`Mut`] will panic in any of the following situations:
///
/// 1) if it is [`Clone::clone`]d more than once
/// 2) if the inner value is accessed after a [`Clone`]
///
/// # Example
///
/// ```
/// # use magic_args::Mut;
/// fn f(mut y: Mut<&mut i32>, x: i32) {
///     **y += 2 * x;
/// }
///
/// let x: i32 = 42;
/// let mut y: i32 = 31;
///
/// magic_args::apply(f, (x, Mut::from(&mut y)));
/// assert_eq!(y, 115);
/// ```
///
/// [`Callable`]: crate::Callable
#[expect(missing_debug_implementations)]
pub struct Mut<T>(Cell<Option<T>>);

impl<T> From<T> for Mut<T> {
    fn from(value: T) -> Self {
        Mut(Cell::new(Some(value)))
    }
}

impl<T> Clone for Mut<T> {
    #[track_caller]
    fn clone(&self) -> Self {
        let inner = self.0.replace(None);
        assert!(inner.is_some(), "magic_args::Mut cloned twice");

        Self(Cell::new(inner))
    }
}

impl<T> Mut<T> {
    fn inner_ptr(&self) -> NonNull<Option<T>> {
        let ptr = self.0.as_ptr();
        NonNull::new(ptr).expect("Cell::as_ptr should never return null")
    }

    #[track_caller]
    fn inner_ref(&self) -> &T {
        // SAFETY: We dereference a pointer to the `Option<T>` inside the
        //         `Cell`. The pointer is correctly aligned and non-null.
        #[expect(unsafe_code)]
        let value = unsafe { self.inner_ptr().as_ref() };
        value.as_ref().expect("magic_args::Mut cloned twice")
    }

    #[track_caller]
    #[expect(clippy::mut_from_ref)]
    fn inner_mut(&self) -> &mut T {
        // SAFETY: We dereference a pointer to the `Option<T>` inside the
        //         `Cell`. The pointer is correctly aligned and non-null.
        #[expect(unsafe_code)]
        let value = unsafe { self.inner_ptr().as_mut() };
        value.as_mut().expect("magic_args::Mut cloned twice")
    }

    /// Destruct this [`Mut`] and get the value inside.
    ///
    /// # Panics
    ///
    /// See: [type-level panic docs](Mut#panics).
    #[track_caller]
    pub fn into_inner(self) -> T {
        // SAFETY: We dereference a pointer to the `Option<T>` inside the
        //         `Cell`. The pointer is correctly aligned and non-null.
        #[expect(unsafe_code)]
        let value = unsafe { self.inner_ptr().as_mut() };
        value.take().expect("magic_args::Mut cloned twice")
    }
}

macro_rules! impl_borrow {
    ($T:ty) => {
        impl<T> Borrow<T> for Mut<$T> {
            #[inline]
            fn borrow(&self) -> &T {
                self.inner_ref()
            }
        }

        impl<T> BorrowMut<T> for Mut<$T> {
            #[inline]
            fn borrow_mut(&mut self) -> &mut T {
                self.inner_mut()
            }
        }
    };
}

macro_rules! impl_as_ref {
    ($T:ty) => {
        impl<T> AsRef<T> for Mut<$T> {
            #[inline]
            fn as_ref(&self) -> &T {
                self.inner_ref()
            }
        }

        impl<T> AsMut<T> for Mut<$T> {
            #[inline]
            fn as_mut(&mut self) -> &mut T {
                self.inner_mut()
            }
        }
    };
}

impl_borrow!(T);
impl_borrow!(&mut T);
impl_borrow!(&mut &mut T);
impl_borrow!(&mut &mut &mut T);

impl_as_ref!(T);
impl_as_ref!(&mut T);
impl_as_ref!(&mut &mut T);
impl_as_ref!(&mut &mut &mut T);

impl<T> Deref for Mut<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.inner_ref()
    }
}

impl<T> DerefMut for Mut<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.inner_mut()
    }
}

///////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod tests {
    use super::*;

    use crate::apply;

    #[test]
    fn test_mut() {
        fn f0(_a: i32, b: Mut<i32>) -> i32 {
            *b
        }

        fn f1(_a: i32, mut b: Mut<&mut i32>) -> i32 {
            let b = b.borrow_mut();
            *b
        }

        fn f2(_a: i32, mut b: Mut<&mut &mut i32>) -> i32 {
            let b = b.borrow_mut();
            *b
        }

        fn f3(_a: i32, mut b: Mut<&mut &mut &mut i32>) -> i32 {
            let b = b.borrow_mut();
            *b
        }

        assert_eq!(apply(f0, (42i32, Mut::from(31i32))), 31);
        assert_eq!(apply(f1, (42i32, Mut::from(&mut 31i32))), 31);
        assert_eq!(apply(f2, (42i32, Mut::from(&mut &mut 31i32))), 31);
        assert_eq!(apply(f3, (42i32, Mut::from(&mut &mut &mut 31i32))), 31);
    }
}
