//! Interface to S3 object stores.

use super::{
    CaptureGroupKey, CaptureGroupValue, InnerObject, IteratorFactory, MatchCaptureGroups, Object,
    PathPattern, PatternComponent,
};
use crate::{combinators::Element, stores::CaptureGroup, AkaniError};
use anyhow::Context;
use aws_config;
use aws_sdk_s3;
use std::{
    cell::{RefCell, RefMut},
    collections::{HashMap, HashSet},
    ops::Deref,
    rc::Rc,
};
use tokio::runtime::{self, Runtime};

/// A type that can return a list of objects through an S3-like interface.
pub trait S3Like {
    fn list_objects(
        &self,
        bucket: &str,
        delimiter: Option<&str>,
        max_keys: Option<u64>,
        prefix: Option<&str>,
        continuation_token: Option<&str>,
    ) -> Result<(Vec<S3Object>, Option<ContinuationToken>), anyhow::Error>;
}

/// The S3 object store.
pub struct S3 {
    async_runtime: Runtime,
    s3_client: aws_sdk_s3::Client,
}

impl S3 {
    pub fn new() -> anyhow::Result<Self> {
        let mut builder = runtime::Builder::new_current_thread();
        builder.enable_all();
        let async_runtime = builder.build().context("Failed to build tokio runtime")?;
        let s3_client = async_runtime.block_on(Self::new_client());
        Ok(Self {
            async_runtime,
            s3_client,
        })
    }

    /// Create an [`S3Bucket`] that accesses an object location defined
    /// by `pattern` through `self`.
    pub fn bucket<'a>(
        &'a self,
        name: &'a str,
        pattern: &'a PathPattern,
        settings: S3BucketSettings,
    ) -> anyhow::Result<S3Bucket<'a, Self>> {
        S3Bucket::new(self, name, pattern, settings)
    }

    async fn new_client() -> aws_sdk_s3::Client {
        let config = aws_config::load_from_env().await;
        aws_sdk_s3::Client::new(&config)
    }

    async fn list_objects_internal<'a>(
        request: aws_sdk_s3::operation::list_objects_v2::builders::ListObjectsV2FluentBuilder,
    ) -> Result<(Vec<S3Object>, Option<ContinuationToken>), anyhow::Error> {
        let response = request.send().await?;
        let continuation_token = response.next_continuation_token;
        let objects = response
            .contents
            .into_iter()
            .flat_map(|c| c.into_iter().map(|o| o.try_into()))
            .collect::<anyhow::Result<Vec<_>>>()?;
        log::debug!("Retrieved {} objects from S3", objects.len());
        Ok((objects, continuation_token))
    }
}

impl S3Like for S3 {
    fn list_objects(
        &self,
        bucket: &str,
        delimiter: Option<&str>,
        max_keys: Option<u64>,
        prefix: Option<&str>,
        continuation_token: Option<&str>,
    ) -> Result<(Vec<S3Object>, Option<ContinuationToken>), anyhow::Error> {
        let request = self
            .s3_client
            .list_objects_v2()
            .bucket(bucket)
            .set_delimiter(delimiter.map(|s| s.to_string()))
            .set_max_keys(max_keys.map(|n| n as i32))
            .set_prefix(prefix.map(|s| s.to_string()))
            .set_continuation_token(continuation_token.map(|s| s.to_string()));
        self.async_runtime
            .block_on(S3::list_objects_internal(request))
    }
}

type ContinuationToken = String;

#[derive(Debug)]
/// Cache for object retrieval from an S3 bucket.
///
/// Objects are indexed by capture groups for efficient access.
///
/// TODO: benchmark the hash index.
struct S3ObjectCache {
    index: HashMap<CaptureGroupKey, HashMap<CaptureGroupValue, HashSet<ObjectToken>>>,
    objects: Vec<Rc<Object>>,
}

impl S3ObjectCache {
    fn new() -> Self {
        Self {
            index: HashMap::new(),
            objects: Vec::new(),
        }
    }

    /// Fill the cache with objects that match `pattern`.
    fn fill(&mut self, objects: Vec<S3Object>, pattern: &PathPattern) -> anyhow::Result<()> {
        for object in objects {
            // log::info!(
            //     "Checking {} against {}",
            //     s3_object.path(),
            //     pattern.components_string(),
            // );
            if let Ok(object) = object.to_object(pattern) {
                log::debug!("Adding object {:?} to cache", object);
                let idx = self.objects.len();
                // Push each object into `self.objects` and update the index (`self.index`).
                for group in object.capture_groups().groups() {
                    let entry = self
                        .index
                        .entry(group.key.clone())
                        .or_insert_with(HashMap::new);
                    let entry = entry
                        .entry(group.value.clone())
                        .or_insert_with(HashSet::new);
                    entry.insert(idx);
                }
                self.objects.push(Rc::new(object));
            } else {
                // Skip if object does not match the pattern.
                log::debug!("Path does not match pattern {:?}", pattern);
                continue;
            }
        }
        Ok(())
    }

    fn clear(&mut self) {
        self.index.clear();
        self.objects.clear();
    }

    fn is_empty(&self) -> bool {
        self.objects.is_empty()
    }

    fn len(&self) -> usize {
        self.objects.len()
    }

    fn get_object(&self, token: ObjectToken) -> Option<Rc<Object>> {
        log::debug!("Getting object with token {:?}", token);
        self.objects.get(token).map(|o| Rc::clone(o))
    }

    /// Get the tokens of objects that match `constraint`. Use [`get_object`] to retrieve the
    /// actual objects.
    fn get_tokens(&self, constraint: &MatchCaptureGroups) -> HashSet<ObjectToken> {
        // If there are no constraints, return all objects.
        let tokens = if constraint.objects().is_empty() {
            return (0..self.objects.len()).collect();
        } else {
            // Extract the token sets beloning to (key, value) pairs from the captures.
            let mut index_sets: Vec<_> = constraint
                .objects()
                .iter()
                .flat_map(|o| {
                    o.capture_groups()
                        .groups()
                        .iter()
                        .map(CaptureGroup::get_key_value)
                })
                .filter_map(|(key, value)| self.index.get(key).and_then(|m| m.get(value)))
                .collect();
            // Start with the smallest set.
            index_sets.sort_unstable_by(|a, b| a.len().cmp(&b.len()).reverse());
            if let Some(first) = index_sets.pop() {
                first
                    .into_iter()
                    .filter(|token| index_sets.iter().rev().all(|set| set.contains(token)))
                    .cloned()
                    .collect()
            } else {
                // No matching objects.
                HashSet::new()
            }
        };
        log::debug!(
            "Returning {:?} tokens for constraint {:?}",
            tokens.len(),
            constraint
        );
        tokens
    }
}

#[derive(Debug, Copy, Clone)]
/// Settings for an [`S3Bucket`].
pub struct S3BucketSettings {
    /// Maximum number of objects to keep in the cache.
    /// Default 10_000.
    pub max_objects_in_cache: Option<u64>,
    /// Maximum number of objects to return in a single request.
    /// Default 1_000.
    pub max_objects_returned_by_request: Option<u64>,
}

impl Default for S3BucketSettings {
    fn default() -> Self {
        Self {
            max_objects_in_cache: None,
            max_objects_returned_by_request: None,
        }
    }
}

impl S3BucketSettings {
    fn max_requests(&self) -> Result<u64, Error> {
        let max_objects_in_cache = self.max_objects_in_cache();
        let max_objects_returned_by_request = self.max_objects_returned_by_request();
        if max_objects_in_cache < max_objects_returned_by_request {
            Err(Error::CacheTooSmall {
                max_objects_in_cache,
                max_objects_returned_by_request,
            })
        } else {
            Ok(max_objects_in_cache / max_objects_returned_by_request)
        }
    }

    fn max_objects_in_cache(&self) -> u64 {
        self.max_objects_in_cache.unwrap_or(10_000)
    }

    fn max_objects_returned_by_request(&self) -> u64 {
        self.max_objects_returned_by_request.unwrap_or(1000)
    }
}

/// Internal representation of an S3 object location.
struct InnerS3Bucket<'a, S> {
    s3: &'a S,
    name: &'a str,
    pattern: &'a PathPattern<'a>,
    cache: S3ObjectCache,
    max_requests: u64,
    max_objects_in_cache: u64,
    max_objects_returned_by_request: u64,
}

impl<'a, S: S3Like> InnerS3Bucket<'a, S> {
    fn new(
        s3: &'a S,
        name: &'a str,
        pattern: &'a PathPattern,
        settings: S3BucketSettings,
    ) -> anyhow::Result<Self> {
        Ok(Self {
            s3,
            name,
            pattern,
            cache: S3ObjectCache::new(),
            max_requests: settings.max_requests()?,
            max_objects_in_cache: settings.max_objects_in_cache(),
            max_objects_returned_by_request: settings.max_objects_returned_by_request(),
        })
    }

    fn get_object(&self, token: ObjectToken) -> Option<Rc<Object>> {
        self.cache.get_object(token)
    }

    /// Retrieves a list of objects from S3 and adds them to the cache.
    /// Returns the continuation token if there are more objects to be retrieved.
    fn download_object_list(
        &mut self,
        continuation_token: Option<&ContinuationToken>,
    ) -> anyhow::Result<Option<ContinuationToken>> {
        // Note that we're not using the constraint here to build the S3 prefix.
        // This is to make fewer requests to S3 and cache more objects by having
        // more general prefixes, e.g. `foo/bar` instead of `foo/bar/baz`.
        let tmp_constraint = MatchCaptureGroups::new();
        let prefix = build_prefix(self.pattern, &tmp_constraint);
        let (objects, continuation_token) = if let Some(continuation_token) = continuation_token {
            log::info!(
                "Bucket {}/{}: downloading objects with continuation token",
                self.name,
                self.pattern.components_string(),
            );
            self.s3.list_objects(
                self.name,
                None,
                Some(self.max_objects_returned_by_request),
                Some(prefix.as_str()),
                Some(continuation_token.as_str()),
            )?
        } else {
            log::info!(
                "Bucket {}/{}: downloading objects with prefix {}",
                self.name,
                self.pattern.components_string(),
                prefix,
            );
            self.s3.list_objects(
                self.name,
                None,
                Some(self.max_objects_returned_by_request),
                Some(prefix.as_str()),
                None,
            )?
        };
        log::info!(
            "Bucket {}/{}: retrieved {} objects",
            self.name,
            self.pattern.components_string(),
            objects.len(),
        );
        self.cache.fill(objects, self.pattern)?;
        debug_assert!(self.cache.len() as u64 <= self.max_objects_in_cache);
        log::info!(
            "Bucket {}/{}: cache contains {} objects",
            self.name,
            self.pattern.components_string(),
            self.cache.len(),
        );
        Ok(continuation_token)
    }

    /// Returns the tokens of objects that match `constraint`.
    fn get_tokens(
        &mut self,
        constraint: &MatchCaptureGroups,
    ) -> anyhow::Result<HashSet<ObjectToken>> {
        log::debug!(
            "Getting tokens for bucket {} with pattern {:?} and constraint {:?}.",
            self.name,
            self.pattern.components_string(),
            constraint
        );
        let objects = self.cache.get_tokens(constraint);
        Ok(objects)
    }

    fn clear_cache(&mut self) {
        log::info!(
            "Bucket {}/{}: clearing cache",
            self.name,
            self.pattern.components_string(),
        );
        self.cache.clear();
    }

    #[cfg(test)]
    fn cache_size(&self) -> usize {
        self.cache.len()
    }

    fn cache_is_empty(&self) -> bool {
        self.cache.is_empty()
    }
}

type Prefix = String;

/// Returns a prefix to be used in an S3 `list-objects-v2` request by replacing
/// the capture groups in `pattern` with values from `constraint`.
fn build_prefix(pattern: &PathPattern, constraint: &MatchCaptureGroups) -> Prefix {
    let prefix = pattern
        .components()
        .iter()
        .scan(false, |stop, item| {
            if *stop {
                None
            } else {
                match item {
                    PatternComponent::RootDir => Some("/"),
                    &PatternComponent::Literal(literal) => Some(literal),
                    &PatternComponent::CaptureGroup(group) => {
                        if let Some(value) = constraint.get(group) {
                            // Replace the capture group with a value.
                            Some(value)
                        } else {
                            // We don't have a value for the capture group.
                            // Find objects that match the prefix so far.
                            *stop = true;
                            Some("/")
                        }
                    }
                    // TODO: For wildcards we may be able to use
                    // `ListObjectsV2FluentBuilder::delimiter` to avoid listing
                    // objects in all subdirectories.
                    // As a downside this would require much more complex queries,
                    // since the `Object`s defined here can be "directories" with
                    // hashes based on their contents which S3 doesn't have as a
                    // concept.
                    PatternComponent::Wildcard | PatternComponent::GlobStar => {
                        // Find objects that match the prefix so far.
                        *stop = true;
                        Some("/")
                    }
                }
            }
        })
        .collect::<Vec<_>>()
        .join("/");
    // Leading and trailing slashes are duplicated in the `join`, remove them.
    let prefix = prefix.strip_prefix("/").unwrap_or(&prefix);
    let prefix = prefix.strip_suffix("/").unwrap_or(prefix);
    log::debug!("Prefix {:?}", prefix);
    prefix.to_string()
}

type ObjectToken = usize;

/// An S3 object location, defined as a bucket combined with
/// a [`PathPattern`].
///
/// Implements [`IteratorFactory`] over chunks of objects
/// ([`S3Chunk`]). The chunks in turn implement [`IteratorFactory`]
/// over objects. This nesting reduces the
/// number of expensive S3 API calls. Instead of each element in
/// factory A going through all chunks in factory B, the elements
/// in chunk 1 for factory A are matched with the elements in
/// chunk 1 for factory B, then chunk 2 for factory B and so on.
/// This reduces the number of API calls from
/// `N_elements_A * N_calls_for_all_elements_in_B` to
/// `N_chunks_A * N_calls_for_all_elements_in_B`.
///
/// TODO: example
pub struct S3Bucket<'a, S> {
    inner: Rc<RefCell<InnerS3Bucket<'a, S>>>,
}

impl<'a, S: S3Like> S3Bucket<'a, S> {
    fn new(
        s3: &'a S,
        name: &'a str,
        pattern: &'a PathPattern,
        settings: S3BucketSettings,
    ) -> anyhow::Result<Self> {
        let bucket = InnerS3Bucket::new(s3, name, pattern, settings)?;
        Ok(Self {
            inner: Rc::new(RefCell::new(bucket)),
        })
    }

    #[cfg(test)]
    fn cache_size(&self) -> anyhow::Result<usize> {
        Ok(self.inner.try_borrow().map(|b| b.cache_size())?)
    }
}

// We need to implement this for `&mut S3Bucket` because `S3BucketIter` uses
// interior mutability to cache objects in `S3Bucket`. The mutable reference
// ensures each `S3Bucket` only has a single `S3BucketIter` active at a time.
impl<'a, 'b, S: S3Like> IteratorFactory<'b, ()> for &'a mut S3Bucket<'b, S> {
    type Item = S3Chunk<'b, S>;

    fn make_iter(&self, _constraint: ()) -> Box<dyn Iterator<Item = Self::Item> + 'b> {
        Box::new(S3ChunkIter::new(self.inner.clone()))
    }
}

/// Iterator over [`S3Chunk`]s.
struct S3ChunkIter<'a, S> {
    bucket: Rc<RefCell<InnerS3Bucket<'a, S>>>,
    counter: usize,
    continuation_token_for_next_chunk: Rc<RefCell<Option<ContinuationToken>>>,
}

impl<'a, S: S3Like> S3ChunkIter<'a, S> {
    fn new(bucket: Rc<RefCell<InnerS3Bucket<'a, S>>>) -> Self {
        let inner = bucket.borrow();
        log::info!(
            "Bucket {}/{}: creating new `S3ChunkIter`",
            inner.name,
            inner.pattern.components_string(),
        );
        Self {
            bucket: bucket.clone(),
            counter: 0,
            continuation_token_for_next_chunk: Rc::new(RefCell::new(None)),
        }
    }
}

impl<'a, S: S3Like> Iterator for S3ChunkIter<'a, S> {
    type Item = S3Chunk<'a, S>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut inner = self.bucket.borrow_mut();
        if self.counter == 0 {
            // First chunk.
            log::info!(
                "Bucket {}/{}: first chunk",
                inner.name,
                inner.pattern.components_string(),
            );
            self.counter += 1;
            assert!(self.continuation_token_for_next_chunk.borrow().is_none());
            let object_iter_init_params = if inner.cache_is_empty() {
                // Retrieve more objects if we're in the first chunk and the
                // cache is empty.
                Some(S3ObjectIterInitParams::DownloadObjectsOnConstruction)
            } else {
                None
            };
            Some(S3Chunk::new(
                self.bucket.clone(),
                self.continuation_token_for_next_chunk.clone(),
                object_iter_init_params,
            ))
        } else if let Some(continuation_token) =
            self.continuation_token_for_next_chunk.borrow_mut().take()
        {
            // Subsequent iterations need a continuation token.
            log::info!(
                "Bucket {}/{}: chunk {}",
                inner.name,
                inner.pattern.components_string(),
                self.counter + 1,
            );
            self.counter += 1;
            // Clear the cache if producing more than one chunk.
            inner.clear_cache();
            // let continuation_token = inner
            //     .download_object_list(Some(&continuation_token))
            //     .unwrap();
            Some(S3Chunk::new(
                self.bucket.clone(),
                self.continuation_token_for_next_chunk.clone(),
                Some(S3ObjectIterInitParams::ContinuationToken(
                    continuation_token,
                )),
            ))
        } else {
            log::info!(
                "Bucket {}/{}: chunks finished",
                inner.name,
                inner.pattern.components_string(),
            );
            // Clear the cache if more than one chunk has been created.
            if self.counter > 1 {
                inner.clear_cache();
            }
            None
        }
    }
}

/// Chunk of S3 objects.
pub struct S3Chunk<'a, S> {
    bucket: Rc<RefCell<InnerS3Bucket<'a, S>>>,
    continuation_token_for_next_chunk: Rc<RefCell<Option<ContinuationToken>>>,
    object_iter_init_params: Rc<RefCell<Option<S3ObjectIterInitParams>>>,
}

impl<'a, S> Clone for S3Chunk<'a, S> {
    fn clone(&self) -> Self {
        Self {
            bucket: self.bucket.clone(),
            continuation_token_for_next_chunk: self.continuation_token_for_next_chunk.clone(),
            object_iter_init_params: self.object_iter_init_params.clone(),
        }
    }
}

impl<'a, S> S3Chunk<'a, S> {
    fn new(
        bucket: Rc<RefCell<InnerS3Bucket<'a, S>>>,
        continuation_token_for_next_chunk: Rc<RefCell<Option<ContinuationToken>>>,
        object_iter_init_params: Option<S3ObjectIterInitParams>,
    ) -> Self {
        Self {
            bucket,
            continuation_token_for_next_chunk,
            object_iter_init_params: Rc::new(RefCell::new(object_iter_init_params)),
        }
    }
}

impl<'a, S> Element<()> for S3Chunk<'a, S> {
    fn constraint(&self) -> Option<()> {
        None
    }
}

impl<'a, S: S3Like> IteratorFactory<'a, MatchCaptureGroups> for S3Chunk<'a, S> {
    type Item = Rc<Object>;

    fn make_iter(
        &self,
        constraint: MatchCaptureGroups,
    ) -> Box<dyn Iterator<Item = Self::Item> + 'a> {
        let bucket_ref: *const _ = Deref::deref(&self.bucket);
        // TODO: benchmark whether the below is necessary. We could pass
        // a cloned `Rc<RefCell<InnerS3Bucket<_>>>` to `S3ObjectIter`
        // instead. The motivation is to keep `RefCell::borrow_mut` out
        // of the hot loop of `S3ObjectIter::next`, but it's not clear
        // whether this is actually a problem.
        //
        // Coerces the `RefMut`s lifetime to 'a (`RefMut<'a, _>`).
        // The `Rc<RefCell<InnerS3Bucket<_>>>` outlives the
        // `S3ObjectIter` which owns the `RefMut`.
        let inner = unsafe { &*bucket_ref }.borrow_mut();
        log::info!(
            "Bucket {}/{}: creating object iterator",
            inner.name,
            inner.pattern.components_string(),
        );
        let max_requests = inner.max_requests;
        Box::new(
            S3ObjectIter::new(
                inner,
                max_requests,
                self.object_iter_init_params.borrow_mut().take(),
                self.continuation_token_for_next_chunk.clone(),
                constraint,
            )
            .unwrap(),
        )
    }
}

enum S3ObjectIterInitParams {
    DownloadObjectsOnConstruction,
    ContinuationToken(ContinuationToken),
}

/// Iterator over S3 objects.
struct S3ObjectIter<'a, S> {
    bucket: Option<RefMut<'a, InnerS3Bucket<'a, S>>>,
    max_requests: u64,
    request_counter: u64,
    tokens: HashSet<ObjectToken>,
    seen_tokens: HashSet<ObjectToken>,
    continuation_token: Option<ContinuationToken>,
    continuation_token_for_next_chunk: Rc<RefCell<Option<ContinuationToken>>>,
    constraint: MatchCaptureGroups,
}

impl<'a, S: S3Like> S3ObjectIter<'a, S> {
    fn new(
        mut bucket: RefMut<'a, InnerS3Bucket<'a, S>>,
        max_requests: u64,
        init_params: Option<S3ObjectIterInitParams>,
        continuation_token_for_next_chunk: Rc<RefCell<Option<ContinuationToken>>>,
        constraint: MatchCaptureGroups,
    ) -> anyhow::Result<Self> {
        let mut request_counter = 0;
        let continuation_token = if let Some(init_params) = init_params {
            match init_params {
                S3ObjectIterInitParams::DownloadObjectsOnConstruction => {
                    // This is the first `S3ObjectIter` constructed for an uncached
                    // first chunk. Start by retrieving new objects.
                    request_counter += 1;
                    bucket.download_object_list(None)?
                }
                S3ObjectIterInitParams::ContinuationToken(continuation_token) => {
                    // This is the first `Self::new` call on a continuing (not first)
                    // chunk.
                    Some(continuation_token)
                }
            }
        } else {
            // This is the case of the first `Self::new` call on a first chunk with
            // objects cached from the previous `S3ChunkIter` iteration or a repeated
            // `Self::new` call on an existing chunk.
            None
        };
        let tokens = bucket.get_tokens(&constraint).unwrap();
        Ok(Self {
            bucket: Some(bucket),
            max_requests,
            request_counter,
            tokens,
            seen_tokens: HashSet::new(),
            continuation_token,
            continuation_token_for_next_chunk,
            constraint,
        })
    }
}

impl<'a, S: S3Like> Iterator for S3ObjectIter<'a, S> {
    type Item = Rc<Object>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(bucket) = &mut self.bucket {
            loop {
                if let Some(&token) = self.tokens.iter().next() {
                    // There are still cached objects.
                    assert!(self.tokens.remove(&token));
                    debug_assert!(!self.seen_tokens.contains(&token));
                    self.seen_tokens.insert(token);
                    break bucket.get_object(token);
                } else if self.request_counter == self.max_requests {
                    log::debug!(
                        "Bucket {}/{}: reached maximum number of requests ({})",
                        bucket.name,
                        bucket.pattern.components_string(),
                        self.max_requests,
                    );
                    // Reached the maximum chunk size.
                    // Store the continuation token for the next chunk.
                    if let Some(continuation_token) = self.continuation_token.take() {
                        let mut continuation_token_for_next_chunk =
                            RefCell::borrow_mut(&self.continuation_token_for_next_chunk);
                        *continuation_token_for_next_chunk = Some(continuation_token);
                    }
                    // Make sure to drop the reference to the bucket. `RefMut` is dynamically
                    // checked, so we can only make another `S3BucketIter` once
                    // the reference has been dropped.
                    self.bucket.take();
                    break None;
                } else if let Some(continuation_token) = &self.continuation_token.take() {
                    // Continue retrieving objects for an existing query.
                    log::info!(
                        "Bucket {}/{}: using continuation token to retrieve more objects",
                        bucket.name,
                        bucket.pattern.components_string(),
                    );
                    let continuation_token = bucket
                        .download_object_list(Some(continuation_token))
                        .unwrap();
                    self.tokens.clear();
                    let new_tokens = bucket.get_tokens(&self.constraint).unwrap();
                    self.tokens.extend(new_tokens.difference(&self.seen_tokens));
                    self.request_counter += 1;
                    self.continuation_token = continuation_token;
                } else {
                    log::debug!(
                        "Bucket {}/{}: object iterator is exhausted",
                        bucket.name,
                        bucket.pattern.components_string(),
                    );
                    // Iterator is exhausted.
                    // Make sure to drop the reference to the bucket. `RefMut` is dynamically
                    // checked, so we can only make another `S3BucketIter` once
                    // the reference has been dropped.
                    self.bucket.take();
                    break None;
                }
            }
        } else {
            // Iterator is exhausted, no more objects.
            None
        }
    }
}

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("invalid object")]
    InvalidObject,
    #[error("dependency error")]
    Dependency(anyhow::Error),
    #[error("capture group '{group_name:?}' is constrained by two values '{constraint1:?}' and '{constraint2:?}'")]
    DuplicateCaptureGroupConstraint {
        group_name: CaptureGroupKey,
        constraint1: CaptureGroupValue,
        constraint2: CaptureGroupValue,
    },
    #[error("`max_objects_in_cache` ({max_objects_in_cache:?}) must be greater than or equal to `max_objects_returned_by_request` ({max_objects_returned_by_request:?})")]
    CacheTooSmall {
        max_objects_in_cache: u64,
        // Default 1_000.
        max_objects_returned_by_request: u64,
    },
}

#[derive(Debug, Clone)]
/// An object in an S3 bucket.
pub struct S3Object {
    key: String,
    // TODO
    _hash: String,
}

impl S3Object {
    /// Returns the key of the object.
    pub fn key(&self) -> &str {
        self.key.as_str()
    }

    fn to_object(self, pattern: &PathPattern) -> Result<Object, AkaniError> {
        let captures = pattern.parse(self.key())?.to_owned();
        Ok(Object::new(InnerObject::S3(self), captures))
    }
}

impl TryFrom<aws_sdk_s3::types::Object> for S3Object {
    type Error = anyhow::Error;

    fn try_from(value: aws_sdk_s3::types::Object) -> Result<Self, Self::Error> {
        Ok(Self {
            key: value.key.ok_or(Error::InvalidObject)?,
            _hash: value.e_tag.ok_or(Error::InvalidObject)?,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::combinators::CartesianProductBuilder;

    use super::super::*;
    use super::*;

    /// Simulates the [`S3`] interface for local testing.
    struct Dummy {
        objects: Vec<S3Object>,
        n_requests: RefCell<u64>,
    }

    impl Dummy {
        fn new(objects: Vec<S3Object>) -> Self {
            Self {
                objects,
                n_requests: RefCell::new(0),
            }
        }

        fn new_numbers() -> Self {
            let (directory_a, directory_b, directory_c) = Self::object_lists();
            let objects: Vec<_> = directory_a
                .chain(directory_b)
                .chain(directory_c)
                .map(|s| S3Object {
                    key: s,
                    _hash: "".to_string(),
                })
                .collect();
            Self::new(objects)
        }

        fn object_lists() -> (
            impl Iterator<Item = String>,
            impl Iterator<Item = String>,
            impl Iterator<Item = String>,
        ) {
            let directory_a = (0..10).into_iter().map(|c| format!("directory_A/{}", c));
            let directory_b = (0..10).into_iter().map(|c| format!("directory_B/{}", c));
            let directory_c = (0..10).into_iter().map(|c| format!("directory_C/{}", c));
            (directory_a, directory_b, directory_c)
        }

        fn bucket<'a>(
            &'a self,
            name: &'a str,
            pattern: &'a PathPattern,
            settings: S3BucketSettings,
        ) -> anyhow::Result<S3Bucket<'a, Self>> {
            S3Bucket::new(self, name, pattern, settings)
        }

        fn n_requests(&self) -> u64 {
            *self.n_requests.borrow()
        }
    }

    impl S3Like for Dummy {
        fn list_objects(
            &self,
            _bucket: &str,
            _delimiter: Option<&str>,
            max_keys: Option<u64>,
            prefix: Option<&str>,
            continuation_token: Option<&str>,
        ) -> Result<(Vec<S3Object>, Option<ContinuationToken>), anyhow::Error> {
            let mut n_requests = self.n_requests.borrow_mut();
            *n_requests += 1;

            let skip = continuation_token
                .map(|token| token.parse::<usize>().unwrap())
                .unwrap_or(0);
            let max_keys = max_keys.unwrap_or(10) as usize;

            let (objects, total_len) = if let Some(prefix) = prefix {
                (
                    self.objects
                        .iter()
                        .filter(|object| object.key.starts_with(prefix))
                        .skip(skip)
                        .take(max_keys)
                        .cloned()
                        .collect::<Vec<_>>(),
                    self.objects
                        .iter()
                        .filter(|object| object.key.starts_with(prefix))
                        .count(),
                )
            } else {
                (
                    self.objects
                        .iter()
                        .skip(skip)
                        .take(max_keys)
                        .cloned()
                        .collect::<Vec<_>>(),
                    self.objects.len(),
                )
            };
            let continuation_token = skip + objects.len();
            let continuation_token = if total_len <= continuation_token {
                None
            } else {
                Some(format!("{}", continuation_token))
            };
            log::warn!(
                "prefix: {:?}, continuation_token: {:?}",
                prefix,
                continuation_token
            );
            Ok((objects, continuation_token))
        }
    }

    // Workaround from https://crates.io/crates/fix-hidden-lifetime-bug
    trait Captures<'__> {}
    impl<T: ?Sized> Captures<'_> for T {}

    /// Returns an iterator over the cartesian product of S3 objects
    /// from `chunk_factories` which iterate over chunks of objects.
    ///
    /// `optional` specifies which factories produce optional elements.
    ///
    /// `external_factory` can be used to add an iterator over objects.
    /// The elements appear last in the cartesian product tuples.
    ///
    /// TODO: make this a public utility function. Example.
    fn make_iter_from_chunks<'a: 'b, 'b, I, Bucket, Chunk, Ext, C, T>(
        chunk_factories: I,
        optional: &[bool],
        external_factory: Option<Ext>,
    ) -> impl Iterator<Item = Vec<Option<T>>> + 'b + Captures<'a>
    where
        I: Iterator<Item = &'b mut Bucket>,
        Bucket: 'a,
        for<'d> &'d mut Bucket: IteratorFactory<'a, (), Item = Chunk>,
        Chunk: IteratorFactory<'a, C, Item = T> + Clone + 'a,
        for<'d> &'d Chunk: Element<()>,
        Ext: IteratorFactory<'a, C, Item = T> + Clone + 'a,
        T: Clone + 'a,
        for<'d> &'d T: Element<C>,
        C: Constraint + 'a,
    {
        // First make a `CartesianProduct` iterating over chunks.
        let mut builder = CartesianProductBuilder::new();
        for (factory, &optional) in chunk_factories.into_iter().zip(optional) {
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
    pub fn no_chunks() {
        let s3 = Dummy::new_numbers();

        let bucket_settings = S3BucketSettings {
            max_objects_returned_by_request: Some(10),
            max_objects_in_cache: Some(10),
        };
        let mut buckets = Vec::new();
        let pattern = PathPattern::new("directory_A/<NUMBER>").unwrap();
        let bucket_a = s3.bucket("bucket_a", &pattern, bucket_settings).unwrap();
        buckets.push(bucket_a);
        let pattern = PathPattern::new("directory_B/<NUMBER>").unwrap();
        let bucket_b = s3.bucket("bucket_b", &pattern, bucket_settings).unwrap();
        buckets.push(bucket_b);
        let pattern = PathPattern::new("directory_C/<NUMBER>").unwrap();
        let bucket_c = s3.bucket("bucket_c", &pattern, bucket_settings).unwrap();
        buckets.push(bucket_c);
        let optional = vec![false, false, false];

        let iter = make_iter_from_chunks(
            buckets.iter_mut(),
            &optional,
            Option::<Vec<Rc<Object>>>::None,
        );
        assert_eq!(iter.count(), 10);
        for bucket in buckets.iter() {
            assert_eq!(bucket.cache_size().unwrap(), 10);
        }
        assert_eq!(s3.n_requests(), 3);
    }

    #[test]
    pub fn chunk_settings_error() {
        let s3 = Dummy::new_numbers();
        let bucket_settings = S3BucketSettings {
            max_objects_returned_by_request: Some(10),
            max_objects_in_cache: Some(1),
        };
        let pattern = PathPattern::new("directory_A/<NUMBER>").unwrap();
        // Cache can't be smaller than number of objects returned by request.
        assert!(s3.bucket("bucket_a", &pattern, bucket_settings).is_err());
    }

    #[test]
    pub fn chunked_left() {
        let s3 = Dummy::new_numbers();

        let bucket_settings = S3BucketSettings {
            max_objects_returned_by_request: Some(10),
            max_objects_in_cache: Some(10),
        };
        let mut buckets = Vec::new();
        let pattern = PathPattern::new("directory_A/<NUMBER>").unwrap();
        let bucket_a = s3
            .bucket(
                "bucket_a",
                &pattern,
                S3BucketSettings {
                    max_objects_returned_by_request: Some(2),
                    max_objects_in_cache: Some(2),
                },
            )
            .unwrap();
        buckets.push(bucket_a);
        let pattern = PathPattern::new("directory_B/<NUMBER>").unwrap();
        let bucket_b = s3.bucket("bucket_b", &pattern, bucket_settings).unwrap();
        buckets.push(bucket_b);
        let pattern = PathPattern::new("directory_C/<NUMBER>").unwrap();
        let bucket_c = s3.bucket("bucket_c", &pattern, bucket_settings).unwrap();
        buckets.push(bucket_c);
        let optional = vec![false, false, false];

        let iter = make_iter_from_chunks(
            buckets.iter_mut(),
            &optional,
            Option::<Vec<Rc<Object>>>::None,
        );
        assert_eq!(iter.count(), 10);
        assert_eq!(buckets[0].cache_size().unwrap(), 0);
        for bucket in buckets.iter().skip(1) {
            assert_eq!(bucket.cache_size().unwrap(), 10);
        }
        // 5 requests for chunked bucket A, 1 for each of the others.
        assert_eq!(s3.n_requests(), 5 + 1 + 1);
    }

    #[test]
    pub fn chunked_middle() {
        let s3 = Dummy::new_numbers();

        let bucket_settings = S3BucketSettings {
            max_objects_returned_by_request: Some(10),
            max_objects_in_cache: Some(10),
        };
        let mut buckets = Vec::new();
        let pattern = PathPattern::new("directory_A/<NUMBER>").unwrap();
        let bucket_a = s3.bucket("bucket_a", &pattern, bucket_settings).unwrap();
        buckets.push(bucket_a);
        let pattern = PathPattern::new("directory_B/<NUMBER>").unwrap();
        let bucket_b = s3
            .bucket(
                "bucket_b",
                &pattern,
                S3BucketSettings {
                    max_objects_returned_by_request: Some(3),
                    max_objects_in_cache: Some(6),
                },
            )
            .unwrap();
        buckets.push(bucket_b);
        let pattern = PathPattern::new("directory_C/<NUMBER>").unwrap();
        let bucket_c = s3.bucket("bucket_c", &pattern, bucket_settings).unwrap();
        buckets.push(bucket_c);
        let optional = vec![false, false, false];

        let iter = make_iter_from_chunks(
            buckets.iter_mut(),
            &optional,
            Option::<Vec<Rc<Object>>>::None,
        );
        assert_eq!(iter.count(), 10);
        assert_eq!(buckets[0].cache_size().unwrap(), 10);
        assert_eq!(buckets[1].cache_size().unwrap(), 0);
        assert_eq!(buckets[2].cache_size().unwrap(), 10);
        // 4 requests for chunked bucket B, 1 for each of the others.
        assert_eq!(s3.n_requests(), 1 + 4 + 1);
    }

    #[test]
    pub fn chunked_right() {
        let s3 = Dummy::new_numbers();

        let bucket_settings = S3BucketSettings {
            max_objects_returned_by_request: Some(10),
            max_objects_in_cache: Some(10),
        };
        let mut buckets = Vec::new();
        let pattern = PathPattern::new("directory_A/<NUMBER>").unwrap();
        let bucket_a = s3.bucket("bucket_a", &pattern, bucket_settings).unwrap();
        buckets.push(bucket_a);
        let pattern = PathPattern::new("directory_B/<NUMBER>").unwrap();
        let bucket_b = s3.bucket("bucket_b", &pattern, bucket_settings).unwrap();
        buckets.push(bucket_b);
        let pattern = PathPattern::new("directory_C/<NUMBER>").unwrap();
        let bucket_c = s3
            .bucket(
                "bucket_c",
                &pattern,
                S3BucketSettings {
                    max_objects_returned_by_request: Some(3),
                    max_objects_in_cache: Some(6),
                },
            )
            .unwrap();
        buckets.push(bucket_c);
        let optional = vec![false, false, false];

        let iter = make_iter_from_chunks(
            buckets.iter_mut(),
            &optional,
            Option::<Vec<Rc<Object>>>::None,
        );
        assert_eq!(iter.count(), 10);
        assert_eq!(buckets[0].cache_size().unwrap(), 10);
        assert_eq!(buckets[1].cache_size().unwrap(), 10);
        assert_eq!(buckets[2].cache_size().unwrap(), 0);
        // 4 requests for chunked bucket C, 1 for each of the others.
        assert_eq!(s3.n_requests(), 1 + 1 + 4);
    }

    #[test]
    pub fn chunked_left_and_middle() {
        let s3 = Dummy::new_numbers();

        let mut buckets = Vec::new();
        let pattern = PathPattern::new("directory_A/<NUMBER>").unwrap();
        let bucket_a = s3
            .bucket(
                "bucket_a",
                &pattern,
                S3BucketSettings {
                    max_objects_returned_by_request: Some(5),
                    max_objects_in_cache: Some(5),
                },
            )
            .unwrap();
        buckets.push(bucket_a);
        let pattern = PathPattern::new("directory_B/<NUMBER>").unwrap();
        let bucket_b = s3
            .bucket(
                "bucket_b",
                &pattern,
                S3BucketSettings {
                    max_objects_returned_by_request: Some(2),
                    max_objects_in_cache: Some(2),
                },
            )
            .unwrap();
        buckets.push(bucket_b);
        let pattern = PathPattern::new("directory_C/<NUMBER>").unwrap();
        let bucket_c = s3
            .bucket(
                "bucket_c",
                &pattern,
                S3BucketSettings {
                    max_objects_returned_by_request: Some(10),
                    max_objects_in_cache: Some(10),
                },
            )
            .unwrap();
        buckets.push(bucket_c);
        let optional = vec![false, false, false];

        let iter = make_iter_from_chunks(
            buckets.iter_mut(),
            &optional,
            Option::<Vec<Rc<Object>>>::None,
        );
        assert_eq!(iter.count(), 10);
        assert_eq!(buckets[0].cache_size().unwrap(), 0);
        assert_eq!(buckets[1].cache_size().unwrap(), 0);
        assert_eq!(buckets[2].cache_size().unwrap(), 10);
        // 2 requests for chunked bucket A, 5 for chunked bucket B for each of A's, 1 for bucket C.
        // C only has 1 request because in the case of one chunk the cache isn't cleared.
        assert_eq!(s3.n_requests(), 2 + (2 * 5) + 1);
    }

    #[test]
    pub fn chunked_multiple_requests_per_chunk() {
        let s3 = Dummy::new_numbers();

        let mut buckets = Vec::new();
        let pattern = PathPattern::new("directory_A/<NUMBER>").unwrap();
        let cache_size_a = 6;
        let request_size_a = 2;
        let bucket_a = s3
            .bucket(
                "bucket_a",
                &pattern,
                S3BucketSettings {
                    max_objects_returned_by_request: Some(request_size_a),
                    max_objects_in_cache: Some(cache_size_a),
                },
            )
            .unwrap();
        buckets.push(bucket_a);
        let pattern = PathPattern::new("directory_B/<NUMBER>").unwrap();
        let cache_size_b = 2;
        let request_size_b = 1;
        let bucket_b = s3
            .bucket(
                "bucket_b",
                &pattern,
                S3BucketSettings {
                    max_objects_returned_by_request: Some(request_size_b),
                    max_objects_in_cache: Some(cache_size_b),
                },
            )
            .unwrap();
        buckets.push(bucket_b);
        let pattern = PathPattern::new("directory_C/<NUMBER>").unwrap();
        let cache_size_c = 6;
        let request_size_c = 4;
        let bucket_c = s3
            .bucket(
                "bucket_c",
                &pattern,
                S3BucketSettings {
                    max_objects_returned_by_request: Some(request_size_c),
                    max_objects_in_cache: Some(cache_size_c),
                },
            )
            .unwrap();
        buckets.push(bucket_c);
        let optional = vec![false, false, false];

        {
            let bucket_iter = buckets.iter_mut();
            let iter =
                make_iter_from_chunks(bucket_iter, &optional, Option::<Vec<Rc<Object>>>::None);
            let (directory_a, directory_b, directory_c) = Dummy::object_lists();
            let target: HashSet<_> = directory_a
                .zip(directory_b)
                .zip(directory_c)
                .map(|((a, b), c)| vec![a, b, c])
                .collect();
            // let _ = env_logger::builder().is_test(true).try_init();
            let mut count = 0;
            for obj in iter {
                count += 1;
                let obj: Vec<_> = obj
                    .into_iter()
                    .map(|o| o.unwrap().path().to_string())
                    .collect();
                assert!(target.contains(&obj));
            }
            assert_eq!(count, 10);
        }
        // 5 requests for chunked bucket A with multiple requests per chunk.
        // For each of A's 2 chunks, 10 requests for bucket B.
        // Out of the 2 * 5 chunk combinations of A and B, only 3 (first A chunk) +
        // 2 (second A chunk) contain matching objects in bucket B. Only these produce
        // requests in bucket C, 3 for each of them.
        assert_eq!(s3.n_requests(), 5 + (2 * 10) + ((3 + 2) * 3));
        assert_eq!(
            s3.n_requests(),
            (10_u64.div_ceil(request_size_a))
                + ((10_u64.div_ceil(cache_size_a)) * (10_u64.div_ceil(request_size_b)))
                + ((3 + 2) * (10_u64.div_ceil(request_size_c)))
        );
    }

    #[test]
    fn s3_params_wildcard() {
        let pattern = PathPattern::new("/foo/<bar>/baz/*").unwrap();
        let captures = vec![CaptureGroup::new("bar".to_string(), "bob".to_string())]
            .into_iter()
            .collect();
        let object = Object::new(InnerObject::Dummy, captures);
        let constraint = std::iter::once(object).collect();
        let prefix = build_prefix(&pattern, &constraint);
        assert_eq!(prefix, "/foo/bob/baz/");
    }

    #[test]
    fn s3_params_globstar() {
        let pattern = PathPattern::new("<bar>/baz/**").unwrap();
        let captures = vec![CaptureGroup::new("bar".to_string(), "bob".to_string())]
            .into_iter()
            .collect();
        let object = Object::new(InnerObject::Dummy, captures);
        let constraint = std::iter::once(object).collect();
        let prefix = build_prefix(&pattern, &constraint);
        assert_eq!(prefix, "bob/baz/");
    }

    #[test]
    fn s3_params_captures() {
        let pattern = PathPattern::new("/foo/<bar>/baz/<qux>/quux.rs").unwrap();
        let captures = vec![
            CaptureGroup::new("bar".to_string(), "bob".to_string()),
            CaptureGroup::new("qux".to_string(), "charlie".to_string()),
        ]
        .into_iter()
        .collect();
        let object = Object::new(InnerObject::Dummy, captures);
        let constraint = std::iter::once(object).collect();
        let prefix = build_prefix(&pattern, &constraint);
        assert_eq!(prefix, "/foo/bob/baz/charlie/quux.rs");
    }

    #[test]
    fn s3_params_no_captures() {
        let pattern = PathPattern::new("/foo/<bar>/baz/<qux>/quux.rs").unwrap();
        let object = Object::new(InnerObject::Dummy, CaptureGroups::new());
        let constraint = std::iter::once(object).collect();
        let prefix = build_prefix(&pattern, &constraint);
        assert_eq!(prefix, "/foo/");
    }
}
