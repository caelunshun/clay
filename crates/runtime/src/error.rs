#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("out of memory in fir heap")]
    OutOfMemory,
    #[error("out of system memory (malloc returned nullptr)")]
    OutOfSystemMemory,
    #[error("{0}")]
    Other(String),
}
