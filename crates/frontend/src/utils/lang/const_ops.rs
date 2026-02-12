use std::{slice, str};

const CAP: usize = 512;

pub struct ConstFmt {
    buffer: [u8; CAP],
    len: usize,
}

impl ConstFmt {
    #[allow(clippy::new_without_default)]
    pub const fn new() -> Self {
        Self {
            buffer: [0; CAP],
            len: 0,
        }
    }

    pub const fn write_str(&mut self, part: &str) {
        let mut i = 0;
        while i < part.len() {
            self.buffer[self.len + i] = part.as_bytes()[i];
            i += 1;
        }

        self.len += part.len();
    }

    pub const fn write(&mut self, ch: char) {
        let mut buf = [0; 4];
        let buf = ch.encode_utf8(&mut buf);
        self.write_str(buf);
    }

    pub const fn finish(&self) -> &str {
        let str_buf = unsafe { slice::from_raw_parts(self.buffer.as_ptr(), self.len) };

        let Ok(str_buf) = str::from_utf8(str_buf) else {
            unreachable!();
        };

        str_buf
    }
}

pub const fn const_str_eq(lhs: &str, rhs: &str) -> bool {
    if lhs.len() != rhs.len() {
        return false;
    }

    let mut i = 0;
    while i < lhs.len() {
        if lhs.as_bytes()[i] != rhs.as_bytes()[i] {
            return false;
        }

        i += 1;
    }

    true
}
