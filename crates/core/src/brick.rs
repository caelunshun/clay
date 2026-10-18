use std::{fmt, io};
use thiserror::Error;

// === Errors === //

#[derive(Debug, Error)]
pub enum BrickReadError {
    #[error(transparent)]
    Header(#[from] BrickReadHeaderError),
}

#[derive(Debug, Error)]
pub enum BrickReadHeaderError {
    #[error("failed to read magic")]
    MagicIo(#[source] io::Error),
    #[error("invalid magic (expected {MAGIC:?}, got {0:?})")]
    MagicInvalid([u8; 8]),
    #[error("failed to read version")]
    VersionIo(#[source] io::Error),
    #[error(
        "unsupported format version {0} (current version is {curr})",
        curr = BrickVersion::CURRENT,
    )]
    VersionInvalid(BrickVersion),
}

#[derive(Debug, Error)]
pub enum BrickReadFooterError {
    #[error("failed to read footer length")]
    ReadLength(#[source] io::Error),
    #[error(
        "footer is longer than file (file is {} byte{} long but footer is {} byte{})",
        file_len,
        if *file_len == 1 { "" } else { "s" },
        footer_len,
        if *footer_len == 1 { "" } else { "s" },
    )]
    FooterTooLong { file_len: u64, footer_len: u32 },
}

// === Definitions === //

pub const MAGIC: [u8; 8] = {
    let mut magic = [0; 8];
    let raw = "clay🧱".as_bytes();
    magic.copy_from_slice(raw);
    magic
};

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct BrickVersion(pub u32);

impl fmt::Display for BrickVersion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl BrickVersion {
    pub const CURRENT: Self = Self(0);
}

pub struct BrickFooter {
    pub chunk_section_size: u32,
    pub entry_section_size: u32,
}

// === Readers === //

pub fn read_header(reader: &mut impl io::Read) -> Result<BrickVersion, BrickReadHeaderError> {
    let read_magic = read_array(&mut *reader).map_err(BrickReadHeaderError::MagicIo)?;

    if read_magic != MAGIC {
        return Err(BrickReadHeaderError::MagicInvalid(read_magic).into());
    }

    let read_version = BrickVersion(read_u32_le(reader).map_err(BrickReadHeaderError::VersionIo)?);

    if read_version != BrickVersion::CURRENT {
        return Err(BrickReadHeaderError::VersionInvalid(read_version).into());
    }

    Ok(read_version)
}

fn read_array<const N: usize>(reader: &mut impl io::Read) -> io::Result<[u8; N]> {
    let mut read_buf = [0; N];
    reader.read_exact(&mut read_buf)?;
    Ok(read_buf)
}

fn read_u32_le(reader: &mut impl io::Read) -> io::Result<u32> {
    read_array(reader).map(u32::from_le_bytes)
}
