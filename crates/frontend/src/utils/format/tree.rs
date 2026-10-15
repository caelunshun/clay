use crate::semantic::infer::ClausePrettyFmtCx;
use std::fmt::{self, Write as _};

// === IndentedFmt === //

pub struct IndentedFmt<'a, 'b> {
    f: &'a mut fmt::Formatter<'b>,
    state: IndentedFmtState,
    level: u32,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum IndentedFmtState {
    AtStart,
    Writing,
    NewlineExplicit,
    NewlineImplicit,
}

impl<'a, 'b> IndentedFmt<'a, 'b> {
    pub fn new(f: &'a mut fmt::Formatter<'b>) -> Self {
        Self {
            f,
            state: IndentedFmtState::AtStart,
            level: 0,
        }
    }

    pub fn level(&self) -> u32 {
        self.level
    }

    pub fn set_level_now(&mut self, level: u32) -> fmt::Result {
        self.state = IndentedFmtState::NewlineImplicit;
        self.level = level;
        Ok(())
    }

    pub fn change_level_now(&mut self, by: i32) -> fmt::Result {
        self.set_level_now(self.level().saturating_add_signed(by))
    }

    pub fn set_level_subsequent(&mut self, level: u32) {
        self.level = level;
    }

    pub fn change_level_subsequent(&mut self, level: i32) {
        self.set_level_subsequent(self.level().saturating_add_signed(level));
    }
}

impl fmt::Write for IndentedFmt<'_, '_> {
    fn write_str(&mut self, mut s: &str) -> fmt::Result {
        while !s.is_empty() {
            // Obtain single-line payload
            let nl = s.find('\n').unwrap_or(s.len());

            let (payload, remaining_s) = s.split_at(nl);

            // Process payload
            if !payload.is_empty() {
                // Insert newline if necessary
                if matches!(
                    self.state,
                    IndentedFmtState::NewlineExplicit | IndentedFmtState::NewlineImplicit
                ) {
                    self.f.write_char('\n')?;
                    self.state = IndentedFmtState::AtStart;
                }

                if self.state == IndentedFmtState::AtStart {
                    for _ in 0..self.level.min(100) {
                        self.f.write_str(" ")?;
                    }

                    self.state = IndentedFmtState::Writing;
                }

                self.f.write_str(payload)?;
            }

            // Process explicit newline and advance
            if !remaining_s.is_empty() {
                s = &remaining_s[1..];

                // A newline was previously queued up. Honor the request because nothing was
                // written.
                if self.state == IndentedFmtState::NewlineExplicit {
                    self.f.write_char('\n')?;
                }

                self.state = IndentedFmtState::NewlineExplicit;
            } else {
                s = "";
            }
        }

        Ok(())
    }
}

// === DebugTree === //

pub trait ToDebugTree: Sized {
    fn to_debug_tree(&self, pretty: &ClausePrettyFmtCx<'_, '_>) -> DebugTree;
}

impl<T: ToDebugTree> ToDebugTree for Vec<T> {
    fn to_debug_tree(&self, pretty: &ClausePrettyFmtCx<'_, '_>) -> DebugTree {
        DebugTree::new().with_sublists(self.iter().map(|v| v.to_debug_tree(pretty)))
    }
}

#[derive(Debug, Clone, Default)]
pub struct DebugTree {
    parts: Vec<DebugTreePart>,
}

#[derive(Debug, Clone)]
enum DebugTreePart {
    Prose(String),
    Sublist(DebugTree),
}

impl DebugTree {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn is_empty(&self) -> bool {
        self.parts.is_empty()
    }

    pub fn push_prose(&mut self, text: impl Into<String>) {
        self.parts.push(DebugTreePart::Prose(text.into()))
    }

    pub fn push_sublist(&mut self, list: impl Into<DebugTree>) {
        let list = list.into();

        if self.is_empty() {
            *self = list;
            return;
        }

        if let [DebugTreePart::Sublist(_)] = &list.parts[..] {
            let [DebugTreePart::Sublist(list)] =
                <[DebugTreePart; 1]>::try_from(list.parts).unwrap()
            else {
                unreachable!();
            };

            self.push_sublist(list);
            return;
        }

        if list.is_empty() {
            return;
        }

        self.parts.push(DebugTreePart::Sublist(list));
    }

    pub fn push_sublists(&mut self, lists: impl IntoIterator<Item = DebugTree>) {
        for list in lists {
            self.push_sublist(list);
        }
    }

    pub fn push_flat_sublist(&mut self, list: impl Into<DebugTree>) {
        self.parts.extend(list.into().parts);
    }

    pub fn push_flat_sublists(&mut self, lists: impl IntoIterator<Item = DebugTree>) {
        for list in lists {
            self.push_flat_sublist(list);
        }
    }

    pub fn with_prose(mut self, text: impl Into<String>) -> Self {
        self.push_prose(text);
        self
    }

    pub fn with_sublist(mut self, list: impl Into<DebugTree>) -> Self {
        self.push_sublist(list);
        self
    }

    pub fn with_sublists(mut self, lists: impl IntoIterator<Item = DebugTree>) -> Self {
        self.push_sublists(lists);
        self
    }

    pub fn with_flat_sublist(mut self, list: impl Into<DebugTree>) -> Self {
        self.push_flat_sublist(list);
        self
    }

    pub fn with_flat_sublists(mut self, lists: impl IntoIterator<Item = DebugTree>) -> Self {
        self.push_flat_sublists(lists);
        self
    }

    pub fn with(mut self, f: impl FnOnce(&mut Self)) -> Self {
        f(&mut self);
        self
    }
}

impl DebugTree {
    fn format(&self, f: &mut IndentedFmt) -> fmt::Result {
        f.write_str("- ")?;
        f.change_level_subsequent(2);

        for part in &self.parts {
            match part {
                DebugTreePart::Prose(line) => {
                    f.write_str(line)?;
                    f.write_char('\n')?;
                }
                DebugTreePart::Sublist(sublist) => {
                    f.change_level_now(2)?;
                    sublist.format(f)?;
                    f.change_level_now(-2)?;
                }
            }
        }

        f.change_level_now(-2)?;

        Ok(())
    }
}

impl fmt::Display for DebugTree {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.format(&mut IndentedFmt::new(f))
    }
}
