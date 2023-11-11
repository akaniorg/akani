//! Provides a [`CartesianProduct`] type to combine iterators.
//!
//! Useful for compiling datums from multiple inputs with
//! named glob capture groups.
//!

/// A type representing a constraint on the elements
/// produced by a [`CartesianProduct`] iterator.
pub trait Constraint: Clone {
    /// Combines the constraint `self` with `other`.
    /// Usually returns the union of the constraints.
    fn combine(self, other: Self) -> Self;
    /// Returns the empty constraint, i.e. all
    /// other elements are allowed.
    fn empty() -> Self;
}

impl Constraint for () {
    fn combine(self, _other: Self) -> Self {
        self
    }

    fn empty() -> Self {
        ()
    }
}

/// A type that can be returned by a [`CartesianProduct`]
/// iterator.
pub trait Element<C> {
    /// Specifies the constraint that the element
    /// imposes on other elements. `None` means
    /// unconstrained.
    fn constraint(&self) -> Option<C> {
        None
    }
}

impl<'a, C, T> Element<C> for &'a T
where
    T: Element<C> + ?Sized,
{
    fn constraint(&self) -> Option<C> {
        (*self).constraint()
    }
}

impl<C> Element<C> for usize {}

impl<C> Element<C> for str {}

impl<C> Element<C> for String {}

// TODO: implement `Element` for more standard types

/// A factory which creates filtered iterators.
///
/// `C` is the constraint that filters the elements.
///
/// `IteratorFactory` is implemented for all cloneable
/// types that implement `IntoIterator`, for example
/// `&Vec`.
pub trait IteratorFactory<'a, C> {
    type Item;

    /// Creates a boxed iterator which produces elements filtered by `constraint`.
    fn make_iter(&self, constraint: C) -> Box<dyn Iterator<Item = Self::Item> + 'a>;
}

impl<'a, T, A, I, C> IteratorFactory<'a, C> for A
where
    A: IntoIterator<IntoIter = I> + Clone + ?Sized,
    I: Iterator<Item = T> + 'a,
    T: 'a,
{
    type Item = T;

    fn make_iter(&self, _constraint: C) -> Box<dyn Iterator<Item = Self::Item> + 'a> {
        Box::new(self.clone().into_iter())
    }
}

/// Wraps an `IteratorFactory` and caches the iterator and latest element.
struct FactoryWrapper<'a, 'b, T, C> {
    // If true, the `FactoryWrapper` can return `None` instead of a value.
    optional: bool,
    // Flags whether `None` has been set as the `value` placeholder for
    // optional `iter`s.
    optional_placeholder_used: bool,
    // Cached most recent value returned by `iter`.
    value: Option<T>,
    // Iterator over elements `T`.
    iter: Box<dyn Iterator<Item = T> + 'a>,
    // The factory which produces `iter`s based on a constraint.
    iter_factory: Box<dyn IteratorFactory<'a, C, Item = T> + 'b>,
}

impl<'a, 'b, T, C> FactoryWrapper<'a, 'b, T, C>
where
    C: Constraint,
    T: 'a,
{
    fn new(iter_factory: Box<dyn IteratorFactory<'a, C, Item = T> + 'b>, optional: bool) -> Self {
        Self {
            optional,
            iter_factory,
            iter: Box::new(std::iter::empty()),
            optional_placeholder_used: false,
            value: None,
        }
    }

    /// Internally replaces the existing `iter` with a new one
    /// adhering to `constraints` by calling [`IteratorFactory::make_iter`].
    fn update_iter<I>(&mut self, constraints: I)
    where
        I: Iterator<Item = Option<C>>,
    {
        // This is the constrain imposed by the other sources
        let external_constraint = constraints
            .filter_map(|c| c)
            .fold(C::empty(), |a, b| a.combine(b));
        self.iter = self.iter_factory.make_iter(external_constraint);
        // Reset tracking variables.
        self.optional_placeholder_used = false;
        self.value = None;
    }

    /// Returns the next element or `None` if the iterator is exhausted.
    /// The inner `Option` is `None` if the element is optional.
    fn next(&mut self) -> Option<Option<()>> {
        let item = self.iter.next();
        if let Some(item) = item {
            self.value = Some(item);
            Some(Some(()))
        } else if self.optional && !self.optional_placeholder_used {
            self.optional_placeholder_used = true;
            self.value = None;
            Some(None)
        } else {
            None
        }
    }
}

/// Builder to create a [`CartesianProduct`] from [`IteratorFactory`]s.
///
/// The order in which factories are added is important: constraints are
/// forward-looking, so a constraint imposed by an element from a later
/// iterator does not affect the elements produced by earlier iterators.
pub struct CartesianProductBuilder<'a, 'b, T, C> {
    reversed_right: Vec<FactoryWrapper<'a, 'b, T, C>>,
    constraint: Option<C>,
}

impl<'a, 'b, T, C> CartesianProductBuilder<'a, 'b, T, C>
where
    T: Clone + 'a,
    for<'c> &'c T: Element<C>,
    C: Constraint,
{
    pub fn new() -> Self {
        CartesianProductBuilder {
            reversed_right: Vec::new(),
            constraint: None,
        }
    }

    /// Adds a factory to the builder. `optional` indicates that the element
    /// from the iterator created by the factory can be replaced by `None`
    /// in the cartesian product if the iterator is exhausted.
    ///
    /// The lifetime `'a` is the lifetime of the iterator, `'b` the lifetime
    /// of the `iter_factory`.
    pub fn add_factory<F>(mut self, iter_factory: F, optional: bool) -> Self
    where
        F: IteratorFactory<'a, C, Item = T> + 'b,
    {
        self.reversed_right
            .push(FactoryWrapper::new(Box::new(iter_factory), optional));
        self
    }

    /// Adds a factory to the builder. `optional` indicates that the element
    /// from the iterator created by the factory can be replaced by `None`
    /// in the cartesian product if the iterator is exhausted.
    ///
    /// The lifetime `'a` is the lifetime of the iterator, `'b` the lifetime
    /// of the `iter_factory`.
    pub fn add_boxed_factory(
        mut self,
        iter_factory: Box<dyn IteratorFactory<'a, C, Item = T> + 'b>,
        optional: bool,
    ) -> Self {
        self.reversed_right
            .push(FactoryWrapper::new(iter_factory, optional));
        self
    }

    /// Adds a constraint for all elements returned by the constructed
    /// [`CartesianProduct`].
    pub fn add_global_constraint(self, constraint: C) -> Self {
        Self {
            constraint: Some(constraint),
            ..self
        }
    }

    /// Builds the [`CartesianProduct`].
    pub fn build(mut self) -> CartesianProduct<'a, 'b, T, C> {
        let mut product = CartesianProduct::new(self.constraint);
        // Reverse the element order in `right` so that the sequences returned by `CartesianProduct`
        // are in the same order as they were `Self::add`ed.
        while let Some(el) = self.reversed_right.pop() {
            product.right.push(el);
        }
        product
    }
}

/// An iterator over the cartesian product of elements returned by
/// the input iterators. Every element is combined with all elements
/// from the other iterators provided they meet the constraints.
///
/// See [`CartesianProductBuilder`] for why the ordering of input iterators
/// is important.
///
/// Iteration is lazy throughout, so input iterators are only advanced
/// to produce the next element. Returns elements of the form `Vec<Option<T>>`
/// where `None` indicates an optional element.
///
/// ```
/// use akani::combinators::{CartesianProduct, CartesianProductBuilder};
///
/// let factories = vec![vec!["a", "b"], vec!["c", "d"], vec!["e"]];
/// let mut builder = CartesianProductBuilder::new();
/// for factory in factories {
///     builder = builder.add_factory(factory.into_iter(), false);
/// }
/// let cartesian_product: CartesianProduct<_, ()> = builder.build();
/// let target = vec![
///     vec![Some("a"), Some("c"), Some("e")],
///     vec![Some("a"), Some("d"), Some("e")],
///     vec![Some("b"), Some("c"), Some("e")],
///     vec![Some("b"), Some("d"), Some("e")],
/// ];
/// for (element, goal) in cartesian_product.zip(target.into_iter()) {
///     assert_eq!(element, goal);
/// }
/// ```
pub struct CartesianProduct<'a, 'b, T, C> {
    left: Vec<FactoryWrapper<'a, 'b, T, C>>,
    right: Vec<FactoryWrapper<'a, 'b, T, C>>,
    global_constraint: Option<C>,
}

impl<'a, 'b, T, C> CartesianProduct<'a, 'b, T, C> {
    fn new(constraint: Option<C>) -> Self {
        CartesianProduct {
            left: Vec::new(),
            right: Vec::new(),
            global_constraint: constraint,
        }
    }
}

impl<'a, 'b, T, C> Iterator for CartesianProduct<'a, 'b, T, C>
where
    T: Clone + 'a,
    for<'c> &'c T: Element<C>,
    C: Constraint,
{
    type Item = Vec<Option<T>>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            // Look at current factory.
            if let Some(mut src) = self.left.pop() {
                if src.next().is_some() {
                    // Iterator still has elements, dial right.
                    if let Some(mut right_src) = self.right.pop() {
                        // Moving right
                        // Push old source
                        self.left.push(src);
                        // Update iter on new factory.
                        right_src.update_iter(
                            // Constraint imposed on all iterators.
                            std::iter::once(self.global_constraint.clone()).chain(
                                // Collect contraints imposed by cached elements.
                                self.left.iter().map(|src| {
                                    src.value.as_ref().map(|e| e.constraint()).flatten()
                                }),
                            ),
                        );
                        self.left.push(right_src);
                    } else {
                        // We're at the last iter, return values.
                        self.left.push(src);
                        return Some(self.left.iter().map(|src| src.value.clone()).collect());
                    }
                } else {
                    // Iterator is exhausted, dial left.
                    self.right.push(src);
                    // If leftmost iterator is exhausted, stop.
                    if self.left.is_empty() {
                        return None;
                    }
                }
            } else {
                // We're at the left end, start filling.
                if let Some(mut right_src) = self.right.pop() {
                    // Update iter on new source
                    right_src.update_iter(
                        // Constraint imposed on all iterators.
                        std::iter::once(self.global_constraint.clone()).chain(
                            // Collect contraints imposed by cached elements.
                            self.left
                                .iter()
                                .map(|src| src.value.as_ref().map(|e| e.constraint()).flatten()),
                        ),
                    );
                    self.left.push(right_src);
                } else {
                    // Empty iterator.
                    return None;
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ops::Deref;

    fn make_cartesian_product<'a: 'b, 'b, I, T, C, A>(
        factories: I,
        optional: impl DoubleEndedIterator<Item = bool>,
        global_constraint: Option<C>,
    ) -> CartesianProduct<'a, 'b, T, C>
    where
        I: Iterator<Item = A>,
        A: IteratorFactory<'a, C, Item = T> + 'b,
        T: Element<C> + Clone + 'a,
        C: Constraint,
    {
        let mut builder = CartesianProductBuilder::new();
        if let Some(constraint) = global_constraint {
            builder = builder.add_global_constraint(constraint);
        }
        for (vec, opt) in factories.zip(optional) {
            builder = builder.add_factory(vec, opt);
        }
        builder.build()
    }

    /// Wrapper type for a slice `&'a [T]`. Needed because slices are unsized,
    /// so they cannot be cast to `& dyn Trait`. `SliceWrapper` is a sized
    /// replacement which supports the cast `&SliceWrapper` -> `&dyn IteratorFactory`.
    struct SliceWrapper<'a, T> {
        slice: &'a [T],
    }

    impl<'a, T> SliceWrapper<'a, T> {
        fn new(slice: &'a [T]) -> Self {
            Self { slice }
        }
    }

    impl<'a, T> IntoIterator for &'a SliceWrapper<'a, T> {
        type Item = &'a T;
        type IntoIter = std::slice::Iter<'a, T>;

        fn into_iter(self) -> Self::IntoIter {
            self.slice.into_iter()
        }
    }

    fn make_slice_wrappers<'a, T>(arr: &[&'a [T]]) -> Vec<SliceWrapper<'a, T>> {
        arr.iter().map(|&row| SliceWrapper::new(row)).collect()
    }

    #[test]
    fn no_factories() {
        let mut iter: CartesianProduct<String, ()> = CartesianProductBuilder::new().build();
        assert!(iter.next().is_none());
    }

    #[test]
    pub fn cross_product() {
        let arr: &[&[_]] = &[&["a", "b"], &["d", "e"], &["g", "h"]];
        let wrappers = make_slice_wrappers(arr);
        // `&SliceWrapper` implements `IteratorFactory` because it implements `IntoIterator`.
        let mut iter =
            make_cartesian_product::<_, _, (), _>(wrappers.iter(), std::iter::repeat(false), None);
        for &one in arr[0].iter() {
            for &two in arr[1].iter() {
                for &three in arr[2].iter() {
                    let element = iter.next().unwrap();
                    assert_eq!(one, *element[0].unwrap());
                    assert_eq!(two, *element[1].unwrap());
                    assert_eq!(three, *element[2].unwrap());
                }
            }
        }
        assert!(iter.next().is_none());
    }

    #[test]
    pub fn empty_factory() {
        let arr: &[&[_]] = &[&["a", "b"], &[], &["g", "h"]];
        let mut wrappers = make_slice_wrappers(arr);
        for _ in 0..3 {
            wrappers.rotate_left(1);
            let mut iter = make_cartesian_product::<_, _, (), _>(
                wrappers.iter(),
                std::iter::repeat(false),
                None,
            );
            assert!(iter.next().is_none());
        }
    }

    #[test]
    pub fn empty_optional_factory_start() {
        let arr: &[&[_]] = &[&[], &["a", "b"], &["g", "h"]];
        let optional: &[_] = &[true, false, false];
        let wrappers = make_slice_wrappers(arr);
        let mut iter =
            make_cartesian_product::<_, _, (), _>(wrappers.iter(), optional.iter().copied(), None);
        for &two in arr[1].iter() {
            for &three in arr[2].iter() {
                let element = iter.next().unwrap();
                assert!(element[0].is_none());
                assert_eq!(two, *element[1].unwrap());
                assert_eq!(three, *element[2].unwrap());
            }
        }
        assert!(iter.next().is_none());
    }

    #[test]
    pub fn empty_optional_factory_middle() {
        let arr: &[&[_]] = &[&["a", "b"], &[], &["g", "h"]];
        let optional: &[_] = &[false, true, false];
        let wrappers = make_slice_wrappers(arr);
        let mut iter =
            make_cartesian_product::<_, _, (), _>(wrappers.iter(), optional.iter().copied(), None);
        for &one in arr[0].iter() {
            for &three in arr[2].iter() {
                let element = iter.next().unwrap();
                assert_eq!(one, *element[0].unwrap());
                assert!(element[1].is_none());
                assert_eq!(three, *element[2].unwrap());
            }
        }
        assert!(iter.next().is_none());
    }

    #[test]
    pub fn empty_optional_factory_end() {
        let arr: &[&[_]] = &[&["a", "b"], &["g", "h"], &[]];
        let optional: &[_] = &[false, false, true];
        let wrappers = make_slice_wrappers(arr);
        let mut iter =
            make_cartesian_product::<_, _, (), _>(wrappers.iter(), optional.iter().copied(), None);
        for &one in arr[0].iter() {
            for &two in arr[1].iter() {
                let element = iter.next().unwrap();
                assert_eq!(one, *element[0].unwrap());
                assert_eq!(two, *element[1].unwrap());
                assert!(element[2].is_none());
            }
        }
        assert!(iter.next().is_none());
    }

    #[test]
    pub fn all_empty_and_optional() {
        let arr: &[&[&str]] = &[&[], &[], &[]];
        let wrappers = make_slice_wrappers(arr);
        let mut iter =
            make_cartesian_product::<_, _, (), _>(wrappers.iter(), std::iter::repeat(true), None);
        assert!(iter.next().unwrap().iter().all(Option::is_none));
        assert!(iter.next().is_none());
    }

    #[derive(Clone)]
    struct DontRepeatMe<'a> {
        seen: Vec<&'a str>,
    }

    impl<'a> DontRepeatMe<'a> {
        fn new(element: &'a str) -> Self {
            Self {
                seen: vec![element],
            }
        }

        fn contains(&self, element: &UniqueElement) -> bool {
            self.seen.contains(&element.inner)
        }
    }

    impl<'a> Constraint for DontRepeatMe<'a> {
        fn combine(self, other: Self) -> Self {
            let mut seen = self.seen;
            seen.extend(other.seen);
            Self { seen }
        }

        fn empty() -> Self {
            Self { seen: Vec::new() }
        }
    }

    #[derive(Debug, PartialEq, Eq, Clone)]
    struct UniqueElement<'a> {
        inner: &'a str,
    }

    impl<'a> UniqueElement<'a> {
        fn new(element: &'a str) -> Self {
            Self { inner: element }
        }
    }

    impl Deref for UniqueElement<'_> {
        type Target = str;

        fn deref(&self) -> &Self::Target {
            self.inner
        }
    }

    impl<'a> Element<DontRepeatMe<'a>> for UniqueElement<'a> {
        fn constraint(&self) -> Option<DontRepeatMe<'a>> {
            Some(DontRepeatMe::new(self.inner))
        }
    }

    #[derive(Debug)]
    /// A factory producing iterators which filter out previously
    /// seen elements.
    struct NoRepeatFactory<'a> {
        inner: Vec<UniqueElement<'a>>,
    }

    impl<'a> FromIterator<UniqueElement<'a>> for NoRepeatFactory<'a> {
        fn from_iter<T: IntoIterator<Item = UniqueElement<'a>>>(iter: T) -> Self {
            Self {
                inner: iter.into_iter().collect(),
            }
        }
    }

    impl<'a> IteratorFactory<'a, DontRepeatMe<'a>> for &'a NoRepeatFactory<'a> {
        type Item = &'a UniqueElement<'a>;

        fn make_iter(
            &self,
            constraint: DontRepeatMe<'a>,
        ) -> Box<dyn Iterator<Item = Self::Item> + 'a> {
            let iter = self.inner.iter().filter(move |&e| !constraint.contains(e));
            Box::new(iter)
        }
    }

    fn compare_unique_element_result<'a, I, J, T>(iter: &mut I, target: J) -> bool
    where
        I: Iterator<Item = Vec<Option<&'a T>>>,
        J: Iterator<Item = Option<&'a str>>,
        T: Deref<Target = str> + 'a + std::fmt::Debug,
    {
        let item = iter.next().unwrap();
        item.into_iter().zip(target).all(|(a, b)| {
            if let (Some(a), Some(b)) = (a, b) {
                a.deref() == b
            } else {
                a.is_none() && b.is_none()
            }
        })
    }

    #[test]
    pub fn constraints() {
        let arr: &[&[_]] = &[&["a", "b"], &["a", "b"], &["a", "b", "c"]];
        let vecs: Vec<NoRepeatFactory> = arr
            .iter()
            .map(|&row| row.iter().map(|e| UniqueElement::new(e)).collect())
            .collect();
        let mut iter = make_cartesian_product(vecs.iter(), std::iter::repeat(false), None);
        let mut target = vec![
            vec![Some("a"), Some("b"), Some("c")],
            vec![Some("b"), Some("a"), Some("c")],
        ];
        for row in target.drain(..) {
            assert!(compare_unique_element_result(&mut iter, row.into_iter()));
        }
        assert!(iter.next().is_none());
    }

    #[test]
    pub fn global_constraint() {
        let arr: &[&[_]] = &[&["a", "b", "d"], &["a", "b"], &["a", "b", "c"]];
        let vecs: Vec<NoRepeatFactory> = arr
            .iter()
            .map(|&row| row.iter().map(|e| UniqueElement::new(e)).collect())
            .collect();
        let global_constraint = DontRepeatMe::new(&"a");
        let mut iter = make_cartesian_product(
            vecs.iter(),
            std::iter::repeat(false),
            Some(global_constraint),
        );
        let target = vec![Some("d"), Some("b"), Some("c")];
        assert!(compare_unique_element_result(&mut iter, target.into_iter()));
        assert!(iter.next().is_none());
    }

    #[test]
    pub fn constraints_and_optionals() {
        let arr: &[&[_]] = &[&["a", "b"], &["a", "b"], &["a", "b", "c"]];
        let optional: &[_] = &[false, true, false];
        let vecs: Vec<NoRepeatFactory> = arr
            .iter()
            .map(|&row| row.iter().map(|e| UniqueElement::new(e)).collect())
            .collect();
        let mut iter = make_cartesian_product(vecs.iter(), optional.iter().copied(), None);
        let mut target = vec![
            vec![Some("a"), Some("b"), Some("c")],
            vec![Some("a"), None, Some("b")],
            vec![Some("a"), None, Some("c")],
            vec![Some("b"), Some("a"), Some("c")],
            vec![Some("b"), None, Some("a")],
            vec![Some("b"), None, Some("c")],
        ];
        for row in target.drain(..) {
            assert!(compare_unique_element_result(&mut iter, row.into_iter()));
        }
        assert!(iter.next().is_none());
    }

    impl<'a> Element<()> for NoRepeatFactory<'a> {
        fn constraint(&self) -> Option<()> {
            None
        }
    }

    #[derive(Debug)]
    /// A factory producing iterators whose elements are
    /// iterator factories themselves. This is useful for
    /// optimising chunked inner iterators, see
    /// [akani::stores::s3] for a real-world example.
    struct ChunkFactory<'a> {
        chunks: Vec<NoRepeatFactory<'a>>,
    }

    impl<'a> FromIterator<&'a [&'a str]> for ChunkFactory<'a> {
        fn from_iter<T: IntoIterator<Item = &'a [&'a str]>>(iter: T) -> Self {
            let mut chunks = Vec::new();
            for chunk in iter {
                let chunk = chunk
                    .iter()
                    .copied()
                    .map(|e| UniqueElement::new(e))
                    .collect();
                chunks.push(chunk);
            }
            Self { chunks }
        }
    }

    impl<'a> IteratorFactory<'a, ()> for &'a ChunkFactory<'a> {
        type Item = &'a NoRepeatFactory<'a>;

        fn make_iter(&self, _: ()) -> Box<dyn Iterator<Item = Self::Item> + 'a> {
            Box::new(self.chunks.iter())
        }
    }

    fn make_iter_from_chunks<'a, I, F, FF, Ext, C, T>(
        chunk_factories: I,
        external_factory: Option<Ext>,
    ) -> impl Iterator<Item = Vec<Option<T>>> + 'a
    where
        I: Iterator<Item = (F, bool)> + 'a,
        F: IteratorFactory<'a, (), Item = FF> + Clone + 'a,
        FF: IteratorFactory<'a, C, Item = T> + Clone + 'a,
        for<'b> &'b FF: Element<()>,
        Ext: IteratorFactory<'a, C, Item = T> + Clone + 'a,
        T: Clone + 'a,
        for<'b> &'b T: Element<C>,
        C: Constraint + 'a,
    {
        // First make a `CartesianProduct` iterating over chunks.
        let mut builder = CartesianProductBuilder::new();
        for (factory, optional) in chunk_factories.map(|t| t.clone()) {
            builder = builder.add_factory(factory, optional);
        }
        let chunk_iter = builder.build();
        // Then flatten each chunk to finally iterate over elements.
        chunk_iter.flat_map(move |v| {
            let mut builder = CartesianProductBuilder::new();
            for chunk in v.into_iter() {
                if let Some(chunk) = chunk {
                    builder = builder.add_factory(chunk, false);
                } else {
                    builder = builder.add_factory(std::iter::empty(), true);
                }
            }
            if let Some(ext) = external_factory.clone() {
                builder = builder.add_factory(ext, false);
            }
            builder.build()
        })
    }

    #[test]
    pub fn chunked() {
        let arr: &[&[&[_]]] = &[&[&["a", "b"]], &[&["c", "d"], &["e", "f"]], &[&["g"]]];
        let vecs: Vec<ChunkFactory> = arr
            .iter()
            .map(|&row| row.iter().copied().collect())
            .collect();
        let mut iter = make_iter_from_chunks(
            vecs.iter().zip(std::iter::repeat(false)),
            Option::<&NoRepeatFactory>::None,
        );
        let mut target = vec![
            vec![Some("a"), Some("c"), Some("g")],
            vec![Some("a"), Some("d"), Some("g")],
            vec![Some("b"), Some("c"), Some("g")],
            vec![Some("b"), Some("d"), Some("g")],
            vec![Some("a"), Some("e"), Some("g")],
            vec![Some("a"), Some("f"), Some("g")],
            vec![Some("b"), Some("e"), Some("g")],
            vec![Some("b"), Some("f"), Some("g")],
        ];
        for row in target.drain(..) {
            assert!(compare_unique_element_result(&mut iter, row.into_iter()));
        }
        assert!(iter.next().is_none());
    }

    #[test]
    pub fn chunked_with_external() {
        let arr: &[&[&[_]]] = &[&[&["a", "b"]], &[&["c", "d"], &["e", "f"]]];
        let vecs: Vec<ChunkFactory> = arr
            .iter()
            .map(|&row| row.iter().copied().collect())
            .collect();
        let external: NoRepeatFactory = (&["g"])
            .iter()
            .copied()
            .map(|e| UniqueElement::new(e))
            .collect();
        let mut iter =
            make_iter_from_chunks(vecs.iter().zip(std::iter::repeat(false)), Some(&external));
        let mut target = vec![
            vec![Some("a"), Some("c"), Some("g")],
            vec![Some("a"), Some("d"), Some("g")],
            vec![Some("b"), Some("c"), Some("g")],
            vec![Some("b"), Some("d"), Some("g")],
            vec![Some("a"), Some("e"), Some("g")],
            vec![Some("a"), Some("f"), Some("g")],
            vec![Some("b"), Some("e"), Some("g")],
            vec![Some("b"), Some("f"), Some("g")],
        ];
        for row in target.drain(..) {
            assert!(compare_unique_element_result(&mut iter, row.into_iter()));
        }
        assert!(iter.next().is_none());
    }

    #[test]
    pub fn chunked_with_constraint() {
        let arr: &[&[&[_]]] = &[&[&["a", "b"]], &[&["c", "d"], &["a", "b"]], &[&["d"]]];
        let vecs: Vec<ChunkFactory> = arr
            .iter()
            .map(|&row| row.iter().copied().collect())
            .collect();
        let mut iter = make_iter_from_chunks(
            vecs.iter().zip(std::iter::repeat(false)),
            Option::<&NoRepeatFactory>::None,
        );
        let mut target = vec![
            vec![Some("a"), Some("c"), Some("d")],
            vec![Some("b"), Some("c"), Some("d")],
            vec![Some("a"), Some("b"), Some("d")],
            vec![Some("b"), Some("a"), Some("d")],
        ];
        for row in target.drain(..) {
            assert!(compare_unique_element_result(&mut iter, row.into_iter()));
        }
        assert!(iter.next().is_none());
    }

    #[test]
    pub fn chunked_optional() {
        let arr: &[&[&[_]]] = &[&[&["a", "b"]], &[&["c", "d"], &["e", "f"]], &[&[]]];
        let optional: &[_] = &[false, false, true];
        let vecs: Vec<ChunkFactory> = arr
            .iter()
            .map(|&row| row.iter().copied().collect())
            .collect();
        let mut iter = make_iter_from_chunks(
            vecs.iter().zip(optional.into_iter().copied()),
            Option::<&NoRepeatFactory>::None,
        );
        let mut target = vec![
            vec![Some("a"), Some("c"), None],
            vec![Some("a"), Some("d"), None],
            vec![Some("b"), Some("c"), None],
            vec![Some("b"), Some("d"), None],
            vec![Some("a"), Some("e"), None],
            vec![Some("a"), Some("f"), None],
            vec![Some("b"), Some("e"), None],
            vec![Some("b"), Some("f"), None],
        ];
        for row in target.drain(..) {
            assert!(compare_unique_element_result(&mut iter, row.into_iter()));
        }
        assert!(iter.next().is_none());
    }
}
