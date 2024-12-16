#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("out of memory in Zyon heap")]
    OutOfMemory,
    #[error("out of system memory (malloc returned nullptr)")]
    OutOfSystemMemory,
    #[error("{0}")]
    Other(String),
}
