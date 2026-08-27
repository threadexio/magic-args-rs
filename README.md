# magic-args

"Magic" declarative-style function arguments.

A cursed exercise of the type system.

```rust
use magic_args::apply;

fn f0() { /* ... */ }
fn f1(x: i32) { /* ... */ }
fn f2(x: i32, z: usize) { /* ... */ }
async fn f3(y: &'static str) { /* ... */ }
async fn f4(y: &'static str, x: i32, z: usize) { /* ... */ }

let args = (-42_i32, "🦀", 42_usize);

let _ = apply(f0, &args);
let _ = apply(f1, &args);
let _ = apply(f2, &args);
let _ = apply(f3, &args);
let _ = apply(f4, &args);
```

The original idea for this crate comes from [axum's route handlers], which do this exact
thing with their arguments.

## Quick start

```rust
use magic_args::apply;

fn f(x: usize, z: &str) -> usize { x + z.len() }

let args = (31_i32, "foo", 42_usize);

let y = apply(f, args);
assert_eq!(y, 45);
```

It is also possible to have a custom type as `args` (instead of a tuple).

```rust
use magic_args::{apply, MagicArgs};

fn f(x: usize, z: &str) -> usize { x + z.len() }

#[derive(MagicArgs)]
struct MyArgs(i32, &'static str, usize);

let args = MyArgs(31, "foo", 42);

let y = apply(f, args);
assert_eq!(y, 45);
```

## How it works

The core of this crate is [`Callable`] and [`Args`]. Everything else is only for
convenience and ease of use.

I will now try to _briefly_ explain how this crate works.

### The [`Args`] trait

The [`Args`] trait describes any kind of type that can act as an "argument set". This is
essentially the type which contains every argument available.

The [`Args`] trait has blanket implementations for tuples of up to 32 elements. It is
also possible to turn any type into [`Args`] with the [`macro@MagicArgs`] macro. It _is_
possible to hand-implement [`Args`] but this is not recommended as you must rely on the
internal constructs of this crate that are subject to change at any time.

### The [`Callable`] trait

This is where the magic happens. [`Callable`] describes anything that can be called with
an argument set. It is blanket-implemented for any `FnOnce` with up to 32 arguments.

The trait is defined over $A$ and $T$. $A$ is the argument set needed and $T$ is an
ordered tuple which contains the types of the arguments the function expects to receive.
For example, in the following function:

```no_run
fn f(x: u32, y: i32, z: usize) {}
```

$A$ is any `A: Args<u32> + Args<i32> + Args<usize>` and $T$ is `(u32, i32, usize)`. The
type parameter $T$ is only there to provide disambiguation for the different `impl`s.
Without it, it would be impossible to provide implementations of `Callable<A>` for
`FnOnce()` and `FnOnce(U)` at the same time. This is because the language, at this time,
lacks [specialized trait `impl`s]. With $T$, the implemented trait is `Callable<A, ()>`
for `FnOnce()` and `Callable<A, (U,)>` for `FnOnce(U)` (which are technically different
traits and thus are allowed to coexist with blanket implementations).

### An implementation detail

**NOTE:** This section serves only as a guide for hackers and just to explain how the
crate works. Nothing here is to be considered as a semver-stable API. Consider yourself
warned.

If you tried to implement [`Args`] for a tuple of `(T0, T1)`, it would probably look a bit
like this:

```rust,compile_fail,E0119
use magic_args::Args;

impl<T0: Clone, T1> Args<T0> for (T0, T1) {
    fn get(&self) -> T0 { self.0.clone() }
}

impl<T0, T1: Clone> Args<T1> for (T0, T1) {
    fn get(&self) -> T1 { self.1.clone() }
}
```

Which, as you might have guessed from the red border above, does not work. This is because
the above implementations are not well-defined. Consider the following type, $(i32, i32)$.
What happens when we invoke [`Args::get`] on that type? Do we get back the first or the
second field? This is the edge case the compiler tries to warn us about. As of writing
this crate, there is no support for specifying type bounds like `T0 != T1`. So we can't
just say "where `T0 != T1`" and be done.

There is another, arguably more convuluted way to describe this. If we introduce a
type `Tagged<T, const N: usize>(T)` we can have many "unique" $T$s. This is because
`Tagged<i32, 0>` is not the same as `Tagged<i32, 1>`. We can use this little property
to modify our [`Args`] implementation a bit; instead of returning `T0` or `T1`, we
return `Tagged<T0, 0>` and `Tagged<T1, 1>` respectively. This solves our previous
issue of "conflicting implementations" since we are now implementing what is now 2
different traits; `Args<Tagged<T0, 0>>` and `Args<Tagged<T1, 1>>`. We can now modify the
[`Callable`] `impl`s to take `const N0: usize`, `const N1: usize` and `A: Args<Tagged<T0,
N0>> + Args<Tagged<T1, N1>>`. This solves our issue and allows all implementations
to coexist. For tuples, the `N` constant in `Tagged` is the index of the field. The
[`macro@MagicArgs`] also uses the index of the field for `N`. `N` is there to serve as
a "tag" for each field. Its value does not really matter, only that it is different for
each field.

## Limitations

### Type-level

This crate operates wholly at the type-level. There is no runtime code generated as part
of resolving arguments, etc. This makes the crate very difficult to use in a dynamic
setting.

### Type-unique arguments

You cannot have 2 different instances of the same type as arguments. For example:

```rust,compile_fail,E0284
use magic_args::apply;

fn f(x: i32, y: i32) -> i32 { x + y }

let args: (i32, i32) = (42, 31);
let _y: i32 = apply(f, args);
```

This can be explained with the following example. Consider the following function:

```rust
fn f(x: i32, _y: i32) -> i32 { x }
```

Given only the signature of the function, $f: (i32, i32) \to i32$, can you figure out the
correct order to pass the values $42$ and $31$ such that $f$ returns $42$? Spoiler alert:
No. It is impossible. In this case, it is not clear how we should pass the arguments to
the function. Trying the above will result in a cryptic error message(s). This can be
alleviated however by using a thin wrapper type which semantically conveys the meaning of
the data.

```rust
use magic_args::apply;

#[derive(Clone)]
struct X(pub i32);

#[derive(Clone)]
struct Y(pub i32);

fn f(X(x): X, Y(y): Y) -> i32 { x + y }

let args = (X(42), Y(31));
let y = apply(f, args);
assert_eq!(y, 73);
```

---

Enjoy responsibly!

[specialized trait `impl`s]: https://github.com/rust-lang/rust/issues/31844
[axum's route handlers]: https://docs.rs/axum/latest/axum/handler/index.html
