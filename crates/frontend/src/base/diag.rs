use super::Session;
use crate::{
    base::syntax::{FilePos, SourceFileOrigin, SourceMap, SourceMapFile, Span},
    utils::mem::MappedRc,
};
use derive_where::derive_where;
use std::{
    fmt,
    marker::PhantomData,
    ops,
    sync::atomic::{AtomicBool, Ordering::*},
};

// === Errors === //

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
#[non_exhaustive]
pub struct ErrorGuaranteed;

pub trait EmissionGuarantee {
    const REQUIRES_FATAL: bool;

    fn new_result(err: Option<ErrorGuaranteed>) -> Self;
}

impl EmissionGuarantee for Option<ErrorGuaranteed> {
    const REQUIRES_FATAL: bool = false;

    fn new_result(err: Option<ErrorGuaranteed>) -> Self {
        err
    }
}

impl EmissionGuarantee for ErrorGuaranteed {
    const REQUIRES_FATAL: bool = true;

    fn new_result(err: Option<ErrorGuaranteed>) -> Self {
        err.expect("mismatched emission guarantee")
    }
}

// === Context === //

#[derive(Debug, Default)]
pub struct DiagCtxt {
    error_guaranteed: AtomicBool,
}

impl DiagCtxt {
    pub fn emit<E: EmissionGuarantee>(&self, diag: Diag<E>) -> E {
        if diag.is_fatal() {
            self.error_guaranteed.store(true, Relaxed);
        }

        emit_pretty(
            &Session::fetch().source_map,
            &mut termcolor::StandardStream::stdout(termcolor::ColorChoice::Auto),
            diag.cast_ref(),
        );

        E::new_result(diag.is_fatal().then_some(ErrorGuaranteed))
    }

    pub fn had_error(&self) -> bool {
        self.error_guaranteed.load(Relaxed)
    }
}

// === `Diag` Definition === //

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum Level {
    Bug,
    Fatal,
    Error,
    DelayedBug,
    Warning,
    Note,
    OnceNote,
    Help,
    OnceHelp,
    FailureNote,
}

impl Level {
    pub fn is_fatal(self) -> bool {
        matches!(self, Level::Bug | Level::Fatal | Level::Error)
    }
}

pub type SoftDiag = Diag<Option<ErrorGuaranteed>>;
pub type HardDiag = Diag<ErrorGuaranteed>;

#[derive_where(Debug, Clone)]
#[repr(C)]
pub struct Diag<E: EmissionGuarantee> {
    pub _guar: PhantomData<fn(E) -> E>,
    pub me: LeafDiag,
    pub children: Vec<LeafDiag>,
}

impl<E: EmissionGuarantee> Diag<E> {
    pub fn cast_ref<E2: EmissionGuarantee>(&self) -> &Diag<E2> {
        assert!(!E2::REQUIRES_FATAL || self.is_fatal());

        unsafe { &*(self as *const Diag<E> as *const Diag<E2>) }
    }

    pub fn cast_mut<E2: EmissionGuarantee>(&mut self) -> &mut Diag<E2> {
        assert!(!E2::REQUIRES_FATAL || self.is_fatal());

        unsafe { &mut *(self as *mut Diag<E> as *mut Diag<E2>) }
    }

    pub fn cast<E2: EmissionGuarantee>(self) -> Diag<E2> {
        assert!(!E2::REQUIRES_FATAL || self.is_fatal());

        Diag {
            _guar: PhantomData,
            me: self.me,
            children: self.children,
        }
    }

    pub fn emit(self) -> E {
        Session::fetch().diag.emit(self)
    }
}

impl HardDiag {
    pub fn span_err(span: Span, message: impl fmt::Display) -> Self {
        LeafDiag::span_err(span, message).promote().cast()
    }

    pub fn anon_err(message: impl fmt::Display) -> Self {
        LeafDiag::new(Level::Error, message).promote().cast()
    }
}

impl SoftDiag {
    pub fn new(level: Level, message: impl fmt::Display) -> Self {
        LeafDiag::new(level, message).promote()
    }

    pub fn span_warn(span: Span, message: impl fmt::Display) -> Self {
        LeafDiag::span_warn(span, message).promote()
    }

    pub fn span_note(span: Span, message: impl fmt::Display) -> Self {
        LeafDiag::span_note(span, message).promote()
    }

    pub fn span_once_note(span: Span, message: impl fmt::Display) -> Self {
        LeafDiag::span_once_note(span, message).promote()
    }
}

impl<E: EmissionGuarantee> Diag<E> {
    pub fn primary(mut self, span: Span, message: impl fmt::Display) -> Self {
        self.push_primary(span, message);
        self
    }

    pub fn secondary(mut self, span: Span, message: impl fmt::Display) -> Self {
        self.push_secondary(span, message);
        self
    }

    pub fn push_primary(&mut self, span: Span, message: impl fmt::Display) -> &mut Self {
        self.me.push_primary(span, message);
        self
    }

    pub fn push_secondary(&mut self, span: Span, message: impl fmt::Display) -> &mut Self {
        self.me.push_secondary(span, message);
        self
    }

    pub fn child(mut self, child: LeafDiag) -> Self {
        self.push_child(child);
        self
    }

    pub fn push_child(&mut self, child: LeafDiag) -> &mut Self {
        self.children.push(child);
        self
    }

    pub fn is_fatal(&self) -> bool {
        self.me.is_fatal() || self.children.iter().any(|v| v.is_fatal())
    }
}

#[derive(Debug, Clone)]
pub struct LeafDiag {
    pub level: Level,
    pub message: StyledMessage,
    pub spans: MultiSpan,
}

impl LeafDiag {
    pub fn new(level: Level, message: impl fmt::Display) -> Self {
        Self {
            level,
            message: StyledMessage(message.to_string()),
            spans: MultiSpan::default(),
        }
    }

    pub fn span_err(span: Span, message: impl fmt::Display) -> Self {
        Self::new(Level::Error, message).primary(span, "")
    }

    pub fn span_warn(span: Span, message: impl fmt::Display) -> Self {
        Self::new(Level::Warning, message).primary(span, "")
    }

    pub fn span_note(span: Span, message: impl fmt::Display) -> Self {
        Self::new(Level::Note, message).primary(span, "")
    }

    pub fn span_once_note(span: Span, message: impl fmt::Display) -> Self {
        Self::new(Level::OnceNote, message).primary(span, "")
    }

    pub fn promote(self) -> SoftDiag {
        Diag {
            _guar: PhantomData,
            me: self,
            children: Vec::new(),
        }
    }

    pub fn primary(mut self, span: Span, message: impl fmt::Display) -> Self {
        self.push_primary(span, message);
        self
    }

    pub fn secondary(mut self, span: Span, message: impl fmt::Display) -> Self {
        self.push_secondary(span, message);
        self
    }

    pub fn push_primary(&mut self, span: Span, message: impl fmt::Display) -> &mut Self {
        self.spans
            .primary
            .push((span, StyledMessage(message.to_string())));

        self
    }

    pub fn push_secondary(&mut self, span: Span, message: impl fmt::Display) -> &mut Self {
        self.spans
            .secondary
            .push((span, StyledMessage(message.to_string())));

        self
    }

    pub fn is_fatal(&self) -> bool {
        self.level.is_fatal()
    }
}

#[derive(Debug, Clone, Default)]
pub struct MultiSpan {
    pub primary: Vec<(Span, StyledMessage)>,
    pub secondary: Vec<(Span, StyledMessage)>,
}

// === StyledMessage === //

#[derive(Debug, Clone)]
pub struct StyledMessage(pub String);

// === Emission Backends === //

fn emit_pretty(source_map: &SourceMap, writer: &mut dyn termcolor::WriteColor, diag: &SoftDiag) {
    use codespan_reporting::{
        diagnostic::{Diagnostic, Label, LabelStyle, Severity},
        files::{Error as FilesError, Files},
        term::{Config, emit},
    };

    struct FilesAdapter<'a>(&'a SourceMap);

    impl<'a> Files<'a> for FilesAdapter<'a> {
        type FileId = FilePos;
        type Name = MappedRc<SourceMapFile, SourceFileOrigin>;
        type Source = MappedRc<String, str>;

        fn name(&'a self, id: Self::FileId) -> Result<Self::Name, FilesError> {
            Ok(MappedRc::new(self.0.file(id), |f| f.origin()))
        }

        fn source(&'a self, id: Self::FileId) -> Result<Self::Source, FilesError> {
            Ok(MappedRc::new(self.0.file(id).contents().clone(), |v| {
                v.as_str()
            }))
        }

        fn line_index(&'a self, id: Self::FileId, byte_index: usize) -> Result<usize, FilesError> {
            let file = self.0.file(id);
            Ok(file
                .segmentation()
                .offset_to_loc(FilePos::new(byte_index))
                .line as usize)
        }

        fn line_range(
            &'a self,
            id: Self::FileId,
            line_index: usize,
        ) -> Result<ops::Range<usize>, FilesError> {
            let file = self.0.file(id);

            Ok(file
                .segmentation()
                .line_span(line_index as u32)
                .interpret_byte_range())
        }
    }

    fn convert_leaf(source_map: &SourceMap, diag: &LeafDiag) -> Diagnostic<FilePos> {
        Diagnostic::new(match diag.level {
            Level::Bug => Severity::Bug,
            Level::Fatal => Severity::Error,
            Level::Error => Severity::Error,
            Level::DelayedBug => Severity::Bug,
            Level::Warning => Severity::Warning,
            Level::Note => Severity::Note,
            Level::OnceNote => Severity::Note,
            Level::Help => Severity::Help,
            Level::OnceHelp => Severity::Help,
            Level::FailureNote => Severity::Help,
        })
        .with_message(&diag.message.0)
        .with_labels(
            diag.spans
                .primary
                .iter()
                .map(|(sp, msg)| {
                    let file = source_map.file(sp.lo);

                    Label {
                        style: LabelStyle::Primary,
                        file_id: sp.lo,
                        range: file.start().delta_usize(sp.lo)..file.start().delta_usize(sp.hi),
                        message: msg.0.clone(),
                    }
                })
                .chain(diag.spans.secondary.iter().map(|(sp, msg)| {
                    let file = source_map.file(sp.lo);

                    Label {
                        style: LabelStyle::Secondary,
                        file_id: sp.lo,
                        range: file.start().delta_usize(sp.lo)..file.start().delta_usize(sp.hi),
                        message: msg.0.clone(),
                    }
                }))
                .collect(),
        )
    }

    emit(
        writer,
        &Config::default(),
        &FilesAdapter(source_map),
        &convert_leaf(source_map, &diag.me),
    )
    .unwrap();

    for child in &diag.children {
        emit(
            writer,
            &Config::default(),
            &FilesAdapter(source_map),
            &convert_leaf(source_map, child),
        )
        .unwrap();
    }
}
