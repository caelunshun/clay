use thiserror::Error;

#[derive(Debug, Error)]
pub enum Error {
    #[error("arena full")]
    ArenaIndexOverflow,
}
