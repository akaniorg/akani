//! Interfaces for object stores (currently S3) and utilities
//! to deal with path patterns and capture groups.

use crate::combinators::{Constraint, Element, IteratorFactory};
use crate::AkaniError;
use std::fmt::Display;
use std::rc::Rc;

pub mod s3;

/// The name (key) of a capture group.
pub type CaptureGroupKey = String;

/// A reference to a capture group key.
pub type CaptureGroupKeyRef<'a> = &'a str;

/// The value of a capture group.
pub type CaptureGroupValue = String;

/// A reference to a capture group value.
pub type CaptureGroupValueRef<'a> = &'a str;

#[derive(Debug, Clone, Hash)]
/// Contains a parsed representation of a path split
/// into components and capture groups.
///
/// TODO: example
pub struct PathPattern<'a> {
    components: Vec<PatternComponent<'a>>,
}

impl<'a> PathPattern<'a> {
    /// Parse `pattern` into a [`PathPattern`]. Returns an error
    /// for invalid paths.
    pub fn new(pattern: &'a str) -> Result<Self, AkaniError> {
        let mut components = Vec::new();
        // Leading slash indicates root directory.
        let pattern = pattern
            .strip_prefix("/")
            .map(|p| {
                components.push(PatternComponent::RootDir);
                p
            })
            .unwrap_or(pattern);
        // Parse remaining components
        let component_iter = pattern.split('/').filter_map(|component| {
            // Check if component is a capture group or wildcard.
            component
                .strip_prefix("<")
                .and_then(|s| s.strip_suffix(">"))
                .map(|s| Some(PatternComponent::CaptureGroup(s)))
                .unwrap_or_else(|| {
                    if component.len() == 0 {
                        // Ignore double, triple etc. slashes.
                        None
                    } else if component == "*" {
                        Some(PatternComponent::Wildcard)
                    } else if component == "**" {
                        Some(PatternComponent::GlobStar)
                    } else {
                        Some(PatternComponent::Literal(component))
                    }
                })
        });
        components.extend(component_iter);
        if components.len() == 0 {
            // An empty path pattern doesn't make sense.
            Err(AkaniError::EmptyPathPattern)
        } else {
            Ok(Self { components })
        }
    }

    /// Turns the internal path representation back
    /// into a string.
    pub fn components_string(&self) -> String {
        self.components
            .iter()
            .map(|c| c.to_string())
            .collect::<Vec<_>>()
            .join("/")
    }

    /// Returns the capture groups contained in `path`. Errors indicate
    /// non-matching or invalid paths.
    pub fn parse(&'a self, path: &'a str) -> Result<CaptureGroupsRef<'a>, AkaniError> {
        let mut path_iter = std::iter::once_with(|| {
            // The next iterator removes all slahes, keep the first
            // one to indicate a root dir.
            if path.starts_with("/") {
                Some("/")
            } else {
                None
            }
        })
        .chain(
            // Split on slashes, removing double, triple etc. slashes.
            path.split('/')
                .map(|s| if s.len() == 0 { None } else { Some(s) }),
        )
        .filter_map(|s| s);
        // Compare `path` elements to pattern components.
        let mut component_iter = ReturnCounter::new(self.components.iter());
        let mut path_iter = ReturnCounter::new(&mut path_iter);
        // The order of the `zip` is important for the checks at the end of
        // the function. The first iterator may have been advanced further
        // than the second iterator, but not the other way around.
        // See [`std::iter::Iterator::zip`] for more information.
        let captures: Result<CaptureGroupsRef, _> = (&mut component_iter)
            .zip(&mut path_iter)
            .filter_map(|(pattern_comp, path_comp)| {
                if path_comp == "*" || path_comp == "**" {
                    Some(Err(AkaniError::PathContainsWildcard {
                        path: path.to_string(),
                    }))
                } else {
                    match pattern_comp {
                        &PatternComponent::Literal(pattern_comp) => {
                            // Literals must match.
                            if pattern_comp != path_comp {
                                Some(Err(AkaniError::NonMatchingPath {
                                    path: path.to_string(),
                                    pattern: self.components_string(),
                                }))
                            } else {
                                None
                            }
                        }
                        PatternComponent::RootDir => {
                            // Root dir must match.
                            if path_comp != "/" {
                                Some(Err(AkaniError::NonMatchingPath {
                                    path: path.to_string(),
                                    pattern: self.components_string(),
                                }))
                            } else {
                                None
                            }
                        }
                        &PatternComponent::CaptureGroup(key) => {
                            // Record capture group value.
                            Some(Ok(CaptureGroupRef::new(key, path_comp)))
                        }
                        PatternComponent::Wildcard | PatternComponent::GlobStar => None,
                    }
                }
            })
            .collect();
        // Return early if there is an error.
        let captures = captures?;
        if component_iter.n_returns() > path_iter.n_returns() {
            // The pattern has more components than the path.
            // This means the above `zip` stopped because `component_iter`
            // still returned, but `path_iter` didn't.
            Err(AkaniError::PathShorterThanPattern {
                path: path.to_string(),
                pattern: self.components_string(),
            })
        } else if path_iter.next().is_some() {
            // `path_iter` still returns, but `component_iter` didn't.
            if matches!(self.components.last(), Some(PatternComponent::GlobStar)) {
                // It's fine if the last pattern component is a globstar. `path_iter`
                // can return as many times as it wants.
                Ok(captures)
            } else {
                // In any other case a longer path is not a match.
                Err(AkaniError::PathLongerThanPattern {
                    path: path.to_string(),
                    pattern: self.components_string(),
                })
            }
        } else {
            Ok(captures)
        }
    }

    /// Returns the components of the path pattern.
    fn components(&self) -> &[PatternComponent] {
        &self.components
    }
}

/// An iterator that remembers the number of items it has returned.
struct ReturnCounter<I> {
    iterator: I,
    count: usize,
}

impl<I> ReturnCounter<I> {
    fn new(iterator: I) -> Self {
        Self { iterator, count: 0 }
    }

    /// Returns the number of items returned by the iterator.
    fn n_returns(&self) -> usize {
        self.count
    }
}

impl<I> Iterator for ReturnCounter<I>
where
    I: Iterator,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(item) = self.iterator.next() {
            self.count += 1;
            Some(item)
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
/// Components a path pattern can contain.
enum PatternComponent<'a> {
    CaptureGroup(CaptureGroupKeyRef<'a>),
    Wildcard,
    GlobStar,
    Literal(&'a str),
    RootDir,
}

impl<'a> Display for PatternComponent<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PatternComponent::CaptureGroup(key) => write!(f, "<{}>", key),
            PatternComponent::Wildcard => write!(f, "*"),
            PatternComponent::GlobStar => write!(f, "**"),
            PatternComponent::Literal(s) => write!(f, "{}", s),
            PatternComponent::RootDir => write!(f, "/"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// A capture group in a path pattern.
struct CaptureGroup {
    key: CaptureGroupKey,
    value: CaptureGroupValue,
}

impl CaptureGroup {
    #[cfg(test)]
    fn new(key: CaptureGroupKey, value: CaptureGroupValue) -> Self {
        Self { key, value }
    }

    fn get_key_value(&self) -> (CaptureGroupKeyRef, CaptureGroupValueRef) {
        (self.key.as_str(), self.value.as_str())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// A reference to a capture group in a path pattern.
pub struct CaptureGroupRef<'a> {
    key: CaptureGroupKeyRef<'a>,
    value: CaptureGroupValueRef<'a>,
}

impl<'a> CaptureGroupRef<'a> {
    fn new(key: CaptureGroupKeyRef<'a>, value: &'a str) -> Self {
        Self { key, value }
    }

    fn to_owned(&self) -> CaptureGroup {
        CaptureGroup {
            key: self.key.to_string(),
            value: self.value.to_string(),
        }
    }

    pub fn get_key_value(&self) -> (CaptureGroupKeyRef, CaptureGroupValueRef) {
        (self.key, self.value)
    }
}

impl<'a> From<&'a CaptureGroup> for CaptureGroupRef<'a> {
    fn from(value: &'a CaptureGroup) -> Self {
        Self {
            key: value.key.as_str(),
            value: value.value.as_str(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// A collection of capture groups.
struct CaptureGroups {
    groups: Vec<CaptureGroup>,
}

impl CaptureGroups {
    #[cfg(test)]
    fn new() -> Self {
        Self { groups: Vec::new() }
    }

    fn groups(&self) -> &[CaptureGroup] {
        &self.groups
    }
}

impl FromIterator<CaptureGroup> for CaptureGroups {
    fn from_iter<T: IntoIterator<Item = CaptureGroup>>(iter: T) -> Self {
        Self {
            groups: iter.into_iter().collect(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// A reference to a collection of capture groups.
pub struct CaptureGroupsRef<'a> {
    groups: Vec<CaptureGroupRef<'a>>,
}

impl<'a> CaptureGroupsRef<'a> {
    fn to_owned(&self) -> CaptureGroups {
        CaptureGroups {
            groups: self.groups.iter().map(|g| g.to_owned()).collect(),
        }
    }

    pub fn groups(&self) -> &[CaptureGroupRef<'a>] {
        self.groups.as_slice()
    }
}

impl<'a> FromIterator<CaptureGroupRef<'a>> for CaptureGroupsRef<'a> {
    fn from_iter<T: IntoIterator<Item = CaptureGroupRef<'a>>>(iter: T) -> Self {
        Self {
            groups: iter.into_iter().collect(),
        }
    }
}

impl<'a> From<&'a CaptureGroups> for CaptureGroupsRef<'a> {
    fn from(value: &'a CaptureGroups) -> Self {
        Self {
            groups: value.groups.iter().map(|g| g.into()).collect(),
        }
    }
}

#[derive(Debug)]
/// Wrapper type representing objects from different stores.
pub enum InnerObject {
    #[cfg(feature = "s3")]
    S3(s3::S3Object),
    Dummy,
}

#[derive(Debug)]
/// An object in an object store.
pub struct Object {
    inner: InnerObject,
    captures: CaptureGroups,
}

impl Object {
    fn new(inner: InnerObject, captures: CaptureGroups) -> Self {
        Self { inner, captures }
    }

    fn capture_groups(&self) -> &CaptureGroups {
        &self.captures
    }

    pub fn path(&self) -> &str {
        match &self.inner {
            InnerObject::S3(s3) => s3.key(),
            InnerObject::Dummy => "",
        }
    }
}

#[derive(Debug, Clone)]
/// A constraint requiring that a path's capture groups
/// match those of other paths.
pub struct MatchCaptureGroups {
    objects: Vec<Rc<Object>>,
}

impl MatchCaptureGroups {
    fn new() -> Self {
        Self {
            objects: Vec::new(),
        }
    }

    fn objects(&self) -> &[Rc<Object>] {
        &self.objects
    }

    fn get(&self, key: CaptureGroupKeyRef) -> Option<CaptureGroupValueRef> {
        self.objects
            .iter()
            .flat_map(|o| o.capture_groups().groups())
            .find_map(|g| {
                let (k, v) = g.get_key_value();
                if k == key {
                    Some(v)
                } else {
                    None
                }
            })
    }
}

impl FromIterator<Object> for MatchCaptureGroups {
    fn from_iter<T: IntoIterator<Item = Object>>(iter: T) -> Self {
        Self {
            objects: iter.into_iter().map(Rc::new).collect(),
        }
    }
}

impl Constraint for MatchCaptureGroups {
    fn combine(self, other: Self) -> Self {
        let Self { mut objects } = self;
        // Make sure no capture groups are required to have two
        // different values.
        assert!(!objects
            .iter()
            .flat_map(|o| o.capture_groups().groups())
            .any(|g| {
                other
                    .objects()
                    .iter()
                    .flat_map(|o| o.capture_groups().groups())
                    .any(|og| {
                        let (k, v) = g.get_key_value();
                        let (ok, ov) = og.get_key_value();
                        k == ok && v != ov
                    })
            }));
        objects.extend(other.objects);
        Self { objects }
    }

    fn empty() -> Self {
        Self {
            objects: Vec::new(),
        }
    }
}

impl<'a> Element<MatchCaptureGroups> for &'a Rc<Object> {
    fn constraint(&self) -> Option<MatchCaptureGroups> {
        Some(MatchCaptureGroups {
            objects: vec![Rc::clone(self)],
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn path_pattern() {
        let pattern = PathPattern::new("///foo/////bar//<baz>/💖/qux.rs").unwrap();
        let target = [
            PatternComponent::RootDir,
            PatternComponent::Literal("foo"),
            PatternComponent::Literal("bar"),
            PatternComponent::CaptureGroup("baz"),
            PatternComponent::Literal("💖"),
            PatternComponent::Literal("qux.rs"),
        ];
        assert_eq!(pattern.components(), &target);
    }

    #[test]
    fn empty_path_pattern() {
        assert!(matches!(
            PathPattern::new(""),
            Err(AkaniError::EmptyPathPattern)
        ));
    }

    #[test]
    fn parse() {
        let pattern = PathPattern::new("foo/bar/baz.rs").unwrap();
        let captures = pattern.parse("foo/bar/baz.rs");
        assert!(matches!(captures, Ok(c) if c.groups().is_empty()));
    }

    #[test]
    fn parse_no_match() {
        let pattern = PathPattern::new("foo/bar/baz.rs").unwrap();
        let captures = pattern.parse("foo/baz/bar.rs");
        assert!(matches!(captures, Err(AkaniError::NonMatchingPath { .. })));
    }

    #[test]
    fn parse_invalid_path() {
        let pattern = PathPattern::new("foo/bar/baz.rs").unwrap();
        let captures = pattern.parse("foo/bar/*");
        assert!(matches!(
            captures,
            Err(AkaniError::PathContainsWildcard { .. })
        ));
    }

    #[test]
    fn parse_with_wildcard() {
        let pattern = PathPattern::new("foo/*/baz.rs").unwrap();
        let captures = pattern.parse("foo/bar/baz.rs");
        assert!(matches!(captures, Ok(c) if c.groups().is_empty()));
    }

    #[test]
    fn parse_with_end_wildcard() {
        let pattern = PathPattern::new("foo/bar/*").unwrap();
        let captures = pattern.parse("foo/bar/baz.rs");
        assert!(matches!(captures, Ok(c) if c.groups().is_empty()));
    }

    #[test]
    fn parse_with_capture_groups() {
        let pattern = PathPattern::new("//foo/*/<bar>/baz/<qux>/**").unwrap();
        let captures = pattern.parse("//foo/bob/amy/baz/charlie//quux/corge.rs");
        let target = [
            CaptureGroupRef::new("bar", "amy"),
            CaptureGroupRef::new("qux", "charlie"),
        ];
        assert!(matches!(captures, Ok(c) if c.groups() == &target));
    }

    #[test]
    fn parse_too_long_path() {
        let pattern = PathPattern::new("foo/bar/baz").unwrap();
        let captures = pattern.parse("foo/bar/baz/qux.rs");
        assert!(matches!(
            captures,
            Err(AkaniError::PathLongerThanPattern { .. })
        ));
    }

    #[test]
    fn parse_longer_path_with_globstar() {
        let pattern = PathPattern::new("foo/**").unwrap();
        let captures = pattern.parse("foo/bar/baz.rs");
        assert!(matches!(captures, Ok(c) if c.groups().is_empty()));
    }

    #[test]
    fn parse_too_short_path() {
        let pattern = PathPattern::new("foo/bar/baz.rs").unwrap();
        let captures = pattern.parse("foo/bar");
        assert!(matches!(
            captures,
            Err(AkaniError::PathShorterThanPattern { .. })
        ));
    }
}
