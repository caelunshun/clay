use std::fmt;

pub fn fmt_write(
    sink: &mut (impl ?Sized + fmt::Write),
    f: impl Fn(&mut fmt::Formatter<'_>) -> fmt::Result,
) -> fmt::Result {
    write!(sink, "{}", FormatFn(f))
}

#[derive(Copy, Clone)]
pub struct DebugAsDisplay<T>(pub T);

impl<T: fmt::Display> fmt::Debug for DebugAsDisplay<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<T: fmt::Display> fmt::Display for DebugAsDisplay<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
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
