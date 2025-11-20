use std::{
    fmt::{self, Write as _},
    mem,
};

// === Adapters === //

pub fn fmt_write(
    sink: &mut (impl ?Sized + fmt::Write),
    f: impl Fn(&mut fmt::Formatter<'_>) -> fmt::Result,
) -> fmt::Result {
    write!(sink, "{}", FormatFn(f))
}

#[derive(Copy, Clone)]
pub struct FormatFn<F>(pub F)
where
    F: Fn(&mut fmt::Formatter<'_>) -> fmt::Result;

impl<F> fmt::Debug for FormatFn<F>
where
    F: Fn(&mut fmt::Formatter<'_>) -> fmt::Result,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (self.0)(f)
    }
}

impl<F> fmt::Display for FormatFn<F>
where
    F: Fn(&mut fmt::Formatter<'_>) -> fmt::Result,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (self.0)(f)
    }
}

// === ListFormatter === //

pub const OR_LIST_GLUE: (&str, &str, &str) = (" ", ",", "or");
pub const AND_LIST_GLUE: (&str, &str, &str) = (" ", ",", "and");

pub trait ListFormatGlue: Sized {
    fn space(&self) -> impl fmt::Display;

    fn comma(&self) -> impl fmt::Display;

    fn conjunction(&self) -> impl fmt::Display;

    fn oxford_comma(&self) -> bool {
        true
    }
}

impl<T: ListFormatGlue> ListFormatGlue for &'_ T {
    fn space(&self) -> impl fmt::Display {
        (**self).space()
    }

    fn comma(&self) -> impl fmt::Display {
        (**self).comma()
    }

    fn conjunction(&self) -> impl fmt::Display {
        (**self).conjunction()
    }

    fn oxford_comma(&self) -> bool {
        (**self).oxford_comma()
    }
}

impl<A, B, C> ListFormatGlue for (A, B, C)
where
    A: fmt::Display,
    B: fmt::Display,
    C: fmt::Display,
{
    fn space(&self) -> impl fmt::Display {
        &self.0
    }

    fn comma(&self) -> impl fmt::Display {
        &self.1
    }

    fn conjunction(&self) -> impl fmt::Display {
        &self.2
    }
}

#[derive(Debug, Clone, Default)]
pub struct ListFormatter {
    part_buffers: [String; 2],
    part_count: u8,
    ever_printed_comma: bool,
}

impl ListFormatter {
    pub fn push(
        &mut self,
        sink: &mut (impl ?Sized + fmt::Write),
        part: impl fmt::Display,
        glue: impl ListFormatGlue,
    ) -> fmt::Result {
        // Buffer the next two parts in the list.
        if self.part_count < 2 {
            write!(&mut self.part_buffers[self.part_count as usize], "{part}").unwrap();
            self.part_count += 1;
            return Ok(());
        }

        // We have at least three parts ready—the two in the buffer and the one we were just given—
        // so we can print out the first one with a delimiting comma.

        // Flush out the first buffer and write our part to it.
        let [next, thereafter] = &mut self.part_buffers;
        sink.write_str(next)?;
        next.clear();
        write!(next, "{part}").unwrap();
        mem::swap(next, thereafter);

        // Write our delimiters.
        write!(sink, "{}{}", glue.comma(), glue.space())?;
        self.ever_printed_comma = true;

        Ok(())
    }

    pub fn push_many(
        &mut self,
        sink: &mut (impl ?Sized + fmt::Write),
        parts: impl IntoIterator<Item: fmt::Display>,
        glue: impl ListFormatGlue,
    ) -> fmt::Result {
        for part in parts {
            self.push(sink, part, &glue)?;
        }

        Ok(())
    }

    pub fn finish(
        &mut self,
        sink: &mut (impl ?Sized + fmt::Write),
        glue: impl ListFormatGlue,
    ) -> fmt::Result {
        match self.part_count {
            0 => {
                debug_assert!(!self.ever_printed_comma);
                // (fallthrough)
            }
            1 => {
                debug_assert!(!self.ever_printed_comma);
                sink.write_str(&self.part_buffers[0])?;
            }
            2 => {
                sink.write_str(&self.part_buffers[0])?;

                if glue.oxford_comma() && self.ever_printed_comma {
                    write!(sink, "{}", glue.comma())?;
                }

                write!(
                    sink,
                    "{}{}{}",
                    glue.space(),
                    glue.conjunction(),
                    glue.space()
                )?;

                sink.write_str(&self.part_buffers[1])?;
            }
            _ => unreachable!(),
        }

        Ok(())
    }
}

pub fn format_list_into(
    sink: &mut (impl ?Sized + fmt::Write),
    iter: impl IntoIterator<Item: fmt::Display>,
    glue: impl ListFormatGlue,
) -> fmt::Result {
    let mut formatter = ListFormatter::default();

    for item in iter {
        formatter.push(sink, &item, &glue)?;
    }

    formatter.finish(sink, &glue)
}

pub fn format_list(
    iter: impl IntoIterator<Item: fmt::Display>,
    glue: impl ListFormatGlue,
) -> String {
    let mut sink = String::new();
    format_list_into(&mut sink, iter, glue).unwrap();
    sink
}

// === Tests === //

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn list_formatter_cases() {
        assert_eq!(format_list([] as [&str; 0], OR_LIST_GLUE), "");

        assert_eq!(format_list(["a"], OR_LIST_GLUE), "a");

        assert_eq!(format_list(["a", "b"], OR_LIST_GLUE), "a or b");

        assert_eq!(format_list(["a", "b", "c"], OR_LIST_GLUE), "a, b, or c");

        assert_eq!(
            format_list(["a", "b", "c", "d"], OR_LIST_GLUE),
            "a, b, c, or d"
        );

        assert_eq!(
            format_list(["a", "b", "c", "d", "e"], OR_LIST_GLUE),
            "a, b, c, d, or e"
        );
    }
}
