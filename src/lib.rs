//! A pointer type for heap-allocated objects which heap storage can be re-used.
//!
//! The box can be consumed to drop the current object and re-use the allocated
//! space to store another object, which type may be different. New memory will
//! only be allocated if the new object does not fit within the currently
//! allocated space.
//!
//! Coercion from `Sized` to `!Sized` boxed objects is supported, including on
//! Rust stable.
//!
//! Last but not least: `Pin`ned boxes can be recycled too, which is useful when
//! repeatedly allocating `Future`s.
//!
//! # Examples
//!
//! Store different objects, re-using if possible the previously allocated
//! storage:
//!
//! ```
//! use recycle_box::RecycleBox;
//!
//! // Store an object.
//! let box1 = RecycleBox::new(123u64);
//!
//! // Store a smaller object.
//! let box2 = RecycleBox::recycle(box1, 456u16); // Does not allocate
//!
//! // Store a larger object.
//! let box3 = RecycleBox::recycle(box2, [123u32; 8]); // New memory is allocated
//!
//! // Move out and replace the previous object.
//! let (array3, box4) = RecycleBox::replace(box3, 789u32); // Does not allocate
//!
//! // Drop the current object but preserve the allocated memory for further re-use.
//! // Note that `vacate()` is just an explicit shorthand for `recycle(())`.
//! let box5 = RecycleBox::vacate(box4);
//! ```
//!
//! Re-use the same box for different objects sharing the same trait:
//!
//! ```
//! use std::future::{self, Future};
//! use recycle_box::{RecycleBox, coerce_box};
//!
//! let mut my_box: RecycleBox<dyn Future<Output = i32>> =
//!     coerce_box!(RecycleBox::new(future::ready(42)));
//! my_box = coerce_box!(RecycleBox::new(future::pending()));
//! ```
//!
//! Recycle a pinned box.
//!
//! ```
//! use std::pin::Pin;
//! use recycle_box::RecycleBox;
//!
//! let pinned_box: Pin<_> = RecycleBox::new(42).into();
//! let new_box = RecycleBox::recycle_pinned(pinned_box, "Forty two");
//! ```

#![warn(missing_docs, missing_debug_implementations, unreachable_pub)]

use std::alloc::{self, Layout};
use std::cmp::max;
use std::fmt;
use std::future::Future;
use std::mem::ManuallyDrop;
use std::ops::{Deref, DerefMut};
use std::pin::Pin;
use std::ptr::{self, NonNull};
use std::task::{Context, Poll};

/// A pointer type for heap-allocated objects which heap storage can be
/// re-used.
///
/// See the [module-level documentation](../../doc/recycle_box/index.html) for more.
pub struct RecycleBox<T>
where
    T: ?Sized,
{
    ptr: NonNull<T>, // NonNull ensures covariance with respect to T.
    base_ptr: NonNull<u8>,
    layout: Layout,
}

impl<T> RecycleBox<T> {
    /// Allocates heap memory based on the size of `T` and places `x` into it.
    pub fn new(x: T) -> Self {
        unsafe { Self::with_layout_unchecked(x, Layout::new::<T>()) }
    }

    /// Allocates heap memory based on the specified layout and places `x` into
    /// it.
    ///
    /// If type `T` does not fit within the specified layout, the layout
    /// alignment and size are increased as needed.
    pub fn with_layout(x: T, layout: Layout) -> Self {
        let x_layout = Layout::new::<T>();
        let x_size_margin = if x_layout.align() > layout.align() {
            x_layout.align() - layout.align()
        } else {
            0
        };
        assert!(x_layout.size() <= (std::usize::MAX - x_size_margin));

        let size = max(x_layout.size() + x_size_margin, layout.size());
        let safe_layout = Layout::from_size_align(size, layout.align()).unwrap();

        // Actually build the box.
        // A panic will be triggered on OOM.
        unsafe { Self::with_layout_unchecked(x, safe_layout) }
    }

    /// Allocates heap memory based on the specified layout and places `x` into
    /// it without verifying that the layout can fit type `T`.
    unsafe fn with_layout_unchecked(x: T, layout: Layout) -> Self {
        let base_ptr = if layout.size() == 0 {
            // Do not perform allocation for zero-sized types.
            NonNull::dangling()
        } else {
            // Allocate memory.
            // A panic will be triggered on OOM.
            NonNull::new(alloc::alloc(layout)).unwrap()
        };
        let ptr = compute_ptr(base_ptr.as_ptr(), layout).unwrap(); // will never panic unless the layout is incompatible with T.
        ptr::write(ptr, x);

        Self {
            ptr: NonNull::new_unchecked(ptr),
            base_ptr,
            layout,
        }
    }

    /// Consumes the box and return both the old value and a new box, re-using
    /// if possible the already allocated memory.
    ///
    /// No memory is allocated unless the new object does not fit within the
    /// already allocated memory block.
    pub fn replace<U>(boxed: Self, x: U) -> (T, RecycleBox<U>) {
        let boxed = ManuallyDrop::new(boxed);
        let old: T = unsafe { ptr::read(boxed.ptr.as_ptr()) };

        if let Some(ptr) = compute_ptr(boxed.base_ptr.as_ptr(), boxed.layout) {
            unsafe {
                ptr::write(ptr, x);

                (
                    old,
                    RecycleBox {
                        base_ptr: boxed.base_ptr,
                        ptr: NonNull::new_unchecked(ptr),
                        layout: boxed.layout,
                    },
                )
            }
        } else {
            unsafe {
                if boxed.layout.size() != 0 {
                    alloc::dealloc(boxed.base_ptr.as_ptr(), boxed.layout);
                }

                (old, RecycleBox::new(x))
            }
        }
    }

    /// Consumes the box and return both the old value and a box containing an
    /// empty tuple.
    ///
    /// This is functionally equivalent to calling [`RecycleBox::replace`] with
    /// an empty tuple as argument, but is more explicit when the intent is
    /// specifically to take the contained object while preserving the allocated
    /// memory for further re-use. It may also be slightly more efficient.
    pub fn take(boxed: Self) -> (T, RecycleBox<()>) {
        let boxed = ManuallyDrop::new(boxed);
        let old: T = unsafe { ptr::read(boxed.ptr.as_ptr()) };

        (
            old,
            RecycleBox {
                base_ptr: boxed.base_ptr,
                ptr: NonNull::dangling(),
                layout: boxed.layout,
            },
        )
    }
}

impl<T> RecycleBox<T>
where
    T: ?Sized,
{
    /// Consumes the box and creates another one, re-using if possible the
    /// already allocated memory.
    ///
    /// The current boxed object is dropped. No memory is allocated unless the
    /// new object does not fit within the already allocated memory block.
    pub fn recycle<U>(boxed: Self, x: U) -> RecycleBox<U> {
        if let Some(ptr) = compute_ptr(boxed.base_ptr.as_ptr(), boxed.layout) {
            unsafe {
                let boxed = ManuallyDrop::new(boxed);
                ptr::drop_in_place(boxed.ptr.as_ptr());
                ptr::write(ptr, x);
                RecycleBox {
                    base_ptr: boxed.base_ptr,
                    ptr: NonNull::new_unchecked(ptr),
                    layout: boxed.layout,
                }
            }
        } else {
            drop(boxed);
            RecycleBox::new(x)
        }
    }

    /// Consumes the box and creates another one containing an empty tuple.
    ///
    /// This is functionally equivalent to calling [`RecycleBox::recycle`] with
    /// an empty tuple as argument, but is more explicit when the intent is
    /// specifically to drop the contained object while preserving the allocated
    /// memory for further re-use. It may also be slightly more efficient.
    pub fn vacate(boxed: Self) -> RecycleBox<()> {
        unsafe {
            let boxed = ManuallyDrop::new(boxed);
            ptr::drop_in_place(boxed.ptr.as_ptr());
            RecycleBox {
                base_ptr: boxed.base_ptr,
                ptr: NonNull::dangling(),
                layout: boxed.layout,
            }
        }
    }

    /// Consumes a pinned box and creates another box, re-using if possible the
    /// already allocated memory.
    ///
    /// This is the same as [`RecycleBox::recycle`] but for a pinned `RecycleBox`.
    /// The `Pin` contract is upheld since the current object is dropped before
    /// it is replaced by the new object.
    ///
    /// # Example
    ///
    /// ```
    /// use std::pin::Pin;
    /// use recycle_box::RecycleBox;
    ///
    /// let pinned_box: Pin<_> = RecycleBox::new(42).into();
    /// let new_box = RecycleBox::recycle_pinned(pinned_box, "Forty two");
    /// ```
    pub fn recycle_pinned<U>(boxed: Pin<RecycleBox<T>>, x: U) -> RecycleBox<U> {
        unsafe { Self::recycle(Pin::into_inner_unchecked(boxed), x) }
    }

    /// Consumes a pinned box and creates another box containing an empty tuple.
    ///
    /// This is the same as [`RecycleBox::vacate`] but for a pinned `RecycleBox`.
    /// The `Pin` contract is upheld since the current object is dropped before
    /// it is replaced by an empty tuple.
    ///
    /// # Example
    ///
    /// ```
    /// use std::pin::Pin;
    /// use recycle_box::RecycleBox;
    ///
    /// let pinned_box: Pin<_> = RecycleBox::new(42).into();
    /// let empty_box = RecycleBox::vacate_pinned(pinned_box);
    /// ```
    pub fn vacate_pinned(boxed: Pin<RecycleBox<T>>) -> RecycleBox<()> {
        unsafe { Self::vacate(Pin::into_inner_unchecked(boxed)) }
    }

    /// Constructs a box from raw pointers and a layout.
    ///
    /// The `T` object pointed to and the storage defined by the base pointer
    /// and the layout become owned by the resulting `RecycleBox`.
    ///
    /// # Safety
    ///
    /// The caller is responsible for making sure that the object pointed to
    /// exists, is of the proper type and is within an already allocated memory
    /// block consistent with the specified base pointer and layout. Also, the
    /// user must ensure that ownership of the object and of the allocated
    /// memory is exclusively held by the box.
    pub unsafe fn from_raw_parts(ptr: *mut T, base_ptr: *mut u8, layout: Layout) -> Self {
        Self {
            ptr: NonNull::new_unchecked(ptr),
            base_ptr: NonNull::new_unchecked(base_ptr),
            layout,
        }
    }

    /// Consumes the Box, returning its internal data.
    ///
    /// The caller becomes responsible for dropping the object pointed to and
    /// deallocating the backing storage.
    pub fn into_raw_parts(boxed: Self) -> (*mut T, *mut u8, Layout) {
        let boxed = ManuallyDrop::new(boxed);
        (boxed.ptr.as_ptr(), boxed.base_ptr.as_ptr(), boxed.layout)
    }
}

/// Checks whether type `T` can be stored within the specified layout at the specified address.
///
/// If type `T` does fit, a pointer with an adequately aligned address is
/// returned.
fn compute_ptr<T>(base_ptr: *mut u8, layout: Layout) -> Option<*mut T> {
    // Calculate the offset dictated by the new alignment.
    let value_layout = Layout::new::<T>();
    if layout.size() < value_layout.size() {
        return None;
    }

    // Note that `align_offset` returns usize::MAX when unsuccessful so the
    // below will appropriately return `None` in such case too.
    let offset = base_ptr.align_offset(value_layout.align());
    if offset <= layout.size() - value_layout.size() {
        Some(unsafe { base_ptr.add(offset) } as *mut T)
    } else {
        None
    }
}

unsafe impl<T: Send + ?Sized> Send for RecycleBox<T> {}
unsafe impl<T: Sync + ?Sized> Sync for RecycleBox<T> {}

impl<T> Drop for RecycleBox<T>
where
    T: ?Sized,
{
    fn drop(&mut self) {
        unsafe {
            ptr::drop_in_place(self.ptr.as_ptr());
            if self.layout.size() != 0 {
                alloc::dealloc(self.base_ptr.as_ptr(), self.layout);
            }
        }
    }
}

impl<T> AsRef<T> for RecycleBox<T>
where
    T: ?Sized,
{
    fn as_ref(&self) -> &T {
        // Safety is warranted by unique ownership and covariance with `T`.
        unsafe { self.ptr.as_ref() }
    }
}

impl<T> AsMut<T> for RecycleBox<T>
where
    T: ?Sized,
{
    fn as_mut(&mut self) -> &mut T {
        // Safety is warranted by unique ownership and covariance with `T`.
        unsafe { self.ptr.as_mut() }
    }
}

impl<T> Deref for RecycleBox<T>
where
    T: ?Sized,
{
    type Target = T;

    fn deref(&self) -> &T {
        self.as_ref()
    }
}

impl<T> DerefMut for RecycleBox<T>
where
    T: ?Sized,
{
    fn deref_mut(&mut self) -> &mut T {
        self.as_mut()
    }
}

impl<T> fmt::Display for RecycleBox<T>
where
    T: fmt::Display + ?Sized,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl<T> fmt::Debug for RecycleBox<T>
where
    T: fmt::Debug + ?Sized,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T> fmt::Pointer for RecycleBox<T>
where
    T: ?Sized,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ptr: *const T = &**self;
        fmt::Pointer::fmt(&ptr, f)
    }
}

impl<T> From<RecycleBox<T>> for Pin<RecycleBox<T>>
where
    T: ?Sized,
{
    fn from(boxed: RecycleBox<T>) -> Self {
        // The `Pin` contract is upheld provided that the value pointed to is
        // dropped in place before a new object is allocated. Therefore, the
        // safety of this function depends primarily on the correct
        // implementations of `recycle` and `vacate`.
        unsafe { Pin::new_unchecked(boxed) }
    }
}

impl<F> Future for RecycleBox<F>
where
    F: ?Sized + Future + Unpin,
{
    type Output = F::Output;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        F::poll(Pin::new(&mut *self), cx)
    }
}

/// Macro coercing a `RecycleBox<T>` into a `RecycleBox<U>`, provided that `T`
/// can be coerced to `U`.
///
/// This can be used to obtain a pointer to an unsized type, such as a trait
/// object, from of a `Sized` type.
///
/// # Examples
///
/// Make a boxed object into a boxed trait object:
///
/// ```
/// use recycle_box::{RecycleBox, coerce_box};
/// use std::fmt::Display;
///
/// let x = RecycleBox::new(1234u32);
/// let x_display: RecycleBox<dyn Display> = coerce_box!(x);
///
/// println!("{}", x_display.as_ref())
/// ```
///
/// Reuse the box of a trait object for another object sharing the same trait:
///
/// ```
/// use std::future::{self, Future};
/// use recycle_box::{RecycleBox, coerce_box};
///
/// let mut my_box: RecycleBox<dyn Future<Output = i32>> = coerce_box!(RecycleBox::new(future::ready(42)));
/// my_box = coerce_box!(RecycleBox::new(future::pending()));
/// ```
#[macro_export]
macro_rules! coerce_box {
    ($src:expr) => {{
        let (base_ptr, ptr, layout) = $crate::RecycleBox::into_raw_parts($src);
        unsafe { $crate::RecycleBox::from_raw_parts(base_ptr, ptr, layout) }
    }};
}

#[cfg(test)]
mod tests {
    use crate::RecycleBox;
    use std::cell::Cell;
    use std::fmt::Debug;
    use std::mem;
    use std::rc::Rc;

    trait TestTrait: Debug {
        fn name(&self) -> &'static str;
    }

    #[derive(Debug)]
    struct TestLoad<T> {
        load: T,
        name: &'static str,
        counter: Rc<Cell<usize>>,
    }
    impl<T> TestLoad<T> {
        fn new(load: T, name: &'static str, counter: Rc<Cell<usize>>) -> Self {
            counter.set(counter.get() + 1);
            Self {
                load,
                name,
                counter,
            }
        }
        fn load(&self) -> T
        where
            T: Clone,
        {
            self.load.clone()
        }
    }
    impl<T: Debug> TestTrait for TestLoad<T> {
        fn name(&self) -> &'static str {
            self.name
        }
    }
    impl<T: PartialEq> PartialEq for TestLoad<T> {
        fn eq(&self, other: &Self) -> bool {
            self.load == other.load
        }
    }
    impl<T> Drop for TestLoad<T> {
        fn drop(&mut self) {
            self.counter.set(self.counter.get() - 1);
        }
    }

    #[derive(Debug, PartialEq)]
    struct EmptyTestLoad;
    impl TestTrait for EmptyTestLoad {
        fn name(&self) -> &'static str {
            "Empty load"
        }
    }

    fn has_same_location<T, U>(first: *const T, second: *const U) -> bool {
        fn distance(a: usize, b: usize) -> usize {
            if a > b {
                a - b
            } else {
                b - a
            }
        }

        distance(first as usize, second as usize)
            <= distance(mem::align_of::<T>(), mem::align_of::<U>())
    }

    #[test]
    fn test_new() {
        let counter = Rc::new(Cell::new(0));
        let v = TestLoad::new(5, "A", counter.clone());
        let b = RecycleBox::new(v);
        assert_eq!(b.as_ref().load(), 5);
        assert_eq!(counter.get(), 1);
        drop(b);
        assert_eq!(counter.get(), 0);
    }
    #[test]
    fn test_new_zero_sized() {
        let v = EmptyTestLoad;
        let _b = RecycleBox::new(v);
    }
    #[test]
    fn test_recycle_with_smaller() {
        let counter = Rc::new(Cell::new(0));
        let v1 = TestLoad::new(5.0, "A", counter.clone());
        let v2 = TestLoad::new(3, "B", counter.clone());
        let b1 = RecycleBox::new(v1);
        assert_eq!(counter.get(), 2);
        let b1_ptr = &*b1 as *const TestLoad<f64>;
        let b2 = RecycleBox::recycle(b1, v2);
        assert_eq!(counter.get(), 1);
        assert_eq!(b2.as_ref().load(), 3);
        assert!(has_same_location(b1_ptr, &*b2));
        drop(b2);
        assert_eq!(counter.get(), 0);
    }
    #[test]
    fn test_recycle_with_bigger() {
        let counter = Rc::new(Cell::new(0));
        let v1 = TestLoad::new(5, "A", counter.clone());
        let v2 = TestLoad::new([1; 10], "B", counter.clone());
        let b1 = RecycleBox::new(v1);
        assert_eq!(counter.get(), 2);
        let b2 = RecycleBox::recycle(b1, v2);
        assert_eq!(counter.get(), 1);
        assert_eq!(b2.as_ref().load(), [1; 10]);
        drop(b2);
        assert_eq!(counter.get(), 0);
    }
    #[test]
    fn test_recycle_with_zero_sized() {
        let counter = Rc::new(Cell::new(0));
        let v1 = TestLoad::new(5, "A", counter.clone());
        let v2 = EmptyTestLoad;
        let b1 = RecycleBox::new(v1);
        assert_eq!(counter.get(), 1);
        let b1_ptr = &*b1 as *const TestLoad<i32>;
        let b2 = RecycleBox::recycle(b1, v2);
        assert!(has_same_location(b1_ptr, &*b2));
        assert_eq!(counter.get(), 0);
        assert_eq!(*b2.as_ref(), EmptyTestLoad);
    }
    #[test]
    fn test_recycle_from_zero_sized() {
        let counter = Rc::new(Cell::new(0));
        let v1 = EmptyTestLoad;
        let v2 = TestLoad::new(5, "B", counter.clone());
        let b1 = RecycleBox::new(v1);
        let b2 = RecycleBox::recycle(b1, v2);
        assert_eq!(counter.get(), 1);
        assert_eq!(b2.as_ref().load(), 5);
        drop(b2);
        assert_eq!(counter.get(), 0);
    }
    #[test]
    fn test_vacate() {
        let counter = Rc::new(Cell::new(0));
        let v1 = TestLoad::new(5, "A", counter.clone());
        let b1 = RecycleBox::new(v1);
        assert_eq!(counter.get(), 1);
        let b1_ptr = &*b1 as *const TestLoad<i32>;
        let b2 = RecycleBox::vacate(b1);
        assert_eq!(counter.get(), 0);
        let v2 = TestLoad::new(5, "B", counter.clone());
        let b3 = RecycleBox::recycle(b2, v2);
        assert!(has_same_location(b1_ptr, &*b3));
        assert_eq!(counter.get(), 1);
        assert_eq!(b3.as_ref().load(), 5);
    }
    #[test]
    fn test_replace_with_smaller() {
        let counter = Rc::new(Cell::new(0));
        let v1 = TestLoad::new(5.0, "A", counter.clone());
        let v2 = TestLoad::new(3, "B", counter.clone());
        let b1 = RecycleBox::new(v1);
        assert_eq!(counter.get(), 2);
        let b1_ptr = &*b1 as *const TestLoad<f64>;
        let (v1bis, b2) = RecycleBox::replace(b1, v2);
        assert!(has_same_location(b1_ptr, &*b2));
        assert_eq!(v1bis.load(), 5.0);
        assert_eq!(counter.get(), 2);
        assert_eq!(b2.as_ref().load(), 3);
        drop(b2);
        assert_eq!(counter.get(), 1);
    }
    #[test]
    fn test_replace_with_bigger() {
        let counter = Rc::new(Cell::new(0));
        let v1 = TestLoad::new(5, "A", counter.clone());
        let v2 = TestLoad::new([1; 10], "B", counter.clone());
        let b1 = RecycleBox::new(v1);
        assert_eq!(counter.get(), 2);
        let (v1bis, b2) = RecycleBox::replace(b1, v2);
        assert_eq!(v1bis.load(), 5);
        assert_eq!(counter.get(), 2);
        assert_eq!(b2.as_ref().load(), [1; 10]);
        drop(b2);
        assert_eq!(counter.get(), 1);
    }
    #[test]
    fn test_replace_with_zero_sized() {
        let counter = Rc::new(Cell::new(0));
        let v1 = TestLoad::new(5, "A", counter.clone());
        let v2 = EmptyTestLoad;
        let b1 = RecycleBox::new(v1);
        assert_eq!(counter.get(), 1);
        let b1_ptr = &*b1 as *const TestLoad<i32>;
        let (v1bis, b2) = RecycleBox::replace(b1, v2);
        assert!(has_same_location(b1_ptr, &*b2));
        assert_eq!(v1bis.load(), 5);
        assert_eq!(counter.get(), 1);
        assert_eq!(*b2.as_ref(), EmptyTestLoad);
    }
    #[test]
    fn test_replace_from_zero_sized() {
        let counter = Rc::new(Cell::new(0));
        let v1 = EmptyTestLoad;
        let v2 = TestLoad::new(5, "B", counter.clone());
        let b1 = RecycleBox::new(v1);
        let (v1bis, b2) = RecycleBox::replace(b1, v2);
        assert_eq!(v1bis, EmptyTestLoad);
        assert_eq!(counter.get(), 1);
        assert_eq!(b2.as_ref().load(), 5);
        drop(b2);
        assert_eq!(counter.get(), 0);
    }
    #[test]
    fn test_take() {
        let counter = Rc::new(Cell::new(0));
        let v1 = TestLoad::new(5, "A", counter.clone());
        let b1 = RecycleBox::new(v1);
        assert_eq!(counter.get(), 1);
        let b1_ptr = &*b1 as *const TestLoad<i32>;
        let (v1bis, b2) = RecycleBox::take(b1);
        assert_eq!(v1bis.load(), 5);
        assert_eq!(counter.get(), 1);
        let v2 = TestLoad::new(5, "B", counter.clone());
        let (bempty, b3) = RecycleBox::replace(b2, v2);
        assert!(has_same_location(b1_ptr, &*b3));
        assert_eq!(bempty, ());
        assert_eq!(counter.get(), 2);
        assert_eq!(b3.as_ref().load(), 5);
    }
    #[test]
    fn test_coerce_unsized() {
        let counter = Rc::new(Cell::new(0));
        let v1 = TestLoad::new(0, "A", counter.clone());
        let b1 = RecycleBox::new(v1);
        let mut b_unsized: RecycleBox<dyn TestTrait> = coerce_box!(b1);
        assert_eq!(counter.get(), 1);
        assert_eq!(b_unsized.as_ref().name(), "A");

        let v2 = TestLoad::new([0; 10], "B", counter.clone());
        assert_eq!(counter.get(), 2);
        b_unsized = coerce_box!(RecycleBox::recycle(b_unsized, v2));
        assert_eq!(counter.get(), 1);
        assert_eq!(b_unsized.as_ref().name(), "B");

        let v3 = EmptyTestLoad;
        b_unsized = coerce_box!(RecycleBox::recycle(b_unsized, v3));
        assert_eq!(counter.get(), 0);
        assert_eq!(b_unsized.as_ref().name(), "Empty load");
    }
}
