pub mod combinators;
pub mod stores;

#[derive(thiserror::Error, Debug)]
pub enum AkaniError {
    #[error("empty path pattern")]
    EmptyPathPattern,
    #[error("path contains wildcard: {path:?}")]
    PathContainsWildcard { path: String },
    #[error("path shorter than pattern. Path {path:?} Pattern {pattern:?}")]
    PathShorterThanPattern { path: String, pattern: String },
    #[error("path longer than pattern. Path {path:?} Pattern {pattern:?}")]
    PathLongerThanPattern { path: String, pattern: String },
    #[error("path does not match pattern. Path {path:?} Pattern {pattern:?}")]
    NonMatchingPath { path: String, pattern: String },
}
