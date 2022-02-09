# recycle-box

A pointer type for heap-allocated objects which heap storage can be re-used.

[![Cargo](https://img.shields.io/crates/v/recycle-box.svg)](https://crates.io/crates/recycle-box)
[![Documentation](https://docs.rs/recycle-box/badge.svg)](https://docs.rs/recycle-box)
[![License](https://img.shields.io/badge/license-MIT%2FApache--2.0-blue.svg)](https://github.com/asynchronics/recycle-box#license)

## Overview

The box can be consumed to drop the current object and re-use the allocated
space to store another object, which type may be different. New memory will only
be allocated if the new object does not fit within the currently allocated
space, taking into account both its size and alignment requirements.

Coercion from `Sized` to `!Sized` boxed objects is supported, including on Rust
stable. Last but not least: `Pin`ned boxes can be recycled too, which is useful
when repeatedly allocating `Future`s.

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
recycle-box = "0.1.0"
```

## Examples

Store different objects, re-using if possible the previously allocated storage:

```rust
use recycle_box::RecycleBox;

// Store an object.
let box1 = RecycleBox::new(123u64);

// Store a smaller object.
let box2 = RecycleBox::recycle(box1, 456u16); // Does not allocate

// Store a larger object.
let box3 = RecycleBox::recycle(box2, [123u32; 8]); // New memory is allocated

// Move out and replace the previous object.
let (array3, box4) = RecycleBox::replace(box3, 789u32); // Does not allocate

// Drop the current object but preserve the allocated memory for further re-use.
// Note that `vacate()` is just an explicit shorthand for `recycle(())`.
let box5 = RecycleBox::vacate(box4);
```

Re-use the same box for different objects sharing the same trait:

```rust
use std::future::{self, Future};
use recycle_box::{RecycleBox, coerce_box};

let mut my_box: RecycleBox<dyn Future<Output = i32>> = coerce_box!(RecycleBox::new(future::ready(42)));
my_box = coerce_box!(RecycleBox::new(future::pending()));
```

Recycle a pinned box.

```rust
use std::pin::Pin;
use recycle_box::RecycleBox;

let pinned_box: Pin<_> = RecycleBox::new(42).into();
let new_box = RecycleBox::recycle_pinned(pinned_box, "Forty two");
```

## Safety

This is a low-level primitive and as such its implementation relies on `unsafe`.
Its correctness is assessed with an extensive test suite complemented by the
[MIRI] interpreter.

[MIRI]: https://github.com/rust-lang/miri

## License

This software is licensed under the [Apache License, Version 2.0](LICENSE-APACHE) or the
[MIT license](LICENSE-MIT), at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.