//! The crate's error types.
//!
//! Decoding and validation are one pass, so there is one `Error` covering
//! both. `OpError` stays separate because `opiter` is a self-contained
//! component: a consumer can call `validate_body` on its own and get a
//! rejection reason in its own vocabulary.

#[cfg(not(charon))]
use core::fmt;

/// Why a byte read or a function body was rejected. The correspondence proof
/// distinguishes only accept from reject, so no variant carries a proof
/// obligation; they exist for debugging. Errors are unspecified in both the
/// core spec and the web embedding.
///
/// Shared by `reader` and `opiter`, which is why it lives here.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub enum OpError {
    UnexpectedEof,
    LebTooLong,
    UnrecognizedOpcode,
    InvalidBlockType,
    TypeMismatch,
    EmptyStack,
    StackMismatch,
    UnknownLabel,
    UnknownLocal,
    UnknownGlobal,
    ImmutableGlobal,
    UnknownMemory,
    UnknownFunc,
    UnknownType,
    UnknownTable,
    /// A callee returns more than one value, which Wasm 1.0 has no encoding for.
    TooManyResults,
    /// A byte the specification writes out as a literal zero was not zero.
    ReservedByteNotZero,
    InvalidAlignment,
    TrailingBytes,
    BodyTooLarge,
    /// The consumer of `validate_body_with` declined the body. Not a validity
    /// verdict: the bytes may well be a well-typed function, and this says only
    /// that validation did not finish.
    Visitor(VisitError),
}

/// Why a consumer declined a body it was handed.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub enum VisitError {
    OutOfMemory,
}

/// Why a module was rejected.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone)]
pub enum Error {
    // --- The shape of the binary ---
    /// A byte read failed while decoding the module structure.
    Read(OpError),
    InvalidMagic,
    InvalidVersion,
    UnexpectedEof,
    /// A byte where the binary format allows only specific values: a type
    /// tag, a limits flag, an import or export kind.
    InvalidType(u8),
    /// A section id that is not one this validator knows, in a position where
    /// it cannot be skipped.
    UnknownSection(u8),
    SectionOutOfOrder,
    /// A section's contents did not end exactly where its size prefix said.
    SectionSizeMismatch,
    /// The function and code sections declare different numbers of functions.
    FuncCodeMismatch,
    /// The module declared functions and has no code section.
    ///
    /// Apart from `FuncCodeMismatch` because the two are not the same news to a
    /// consumer reading a module as it arrives: a code section that has not
    /// been reached yet may still turn up, where a code section that declares
    /// the wrong number of entries will not become right.
    MissingCodeSection,
    /// A name was not valid UTF-8 (spec 5.2.4).
    InvalidUtf8,

    // --- Validation ---
    UnknownType(u32),
    UnknownFunc(u32),
    UnknownTable(u32),
    UnknownMemory(u32),
    UnknownGlobal(u32),
    DuplicateExportName,
    LimitsOutOfRange,
    MultipleMemories,
    MultipleTables,
    InvalidStartType,
    MutableGlobalInConstExpr,
    InvalidConstExpr,
    /// A function type returns more than one value, or a function declares
    /// more locals than the implementation allows.
    TooManyResults,
    TooManyLocals,
    ModuleTooLarge,
    /// A function body was rejected by `opiter::validate_body`.
    Body(OpError),
    /// The consumer of a `_with` entry point declined what it was shown. Not a
    /// validity verdict, the same way `OpError::Visitor` is not: the module may
    /// well be valid, and this says only that decoding did not finish.
    Visitor(VisitError),
}

impl From<OpError> for Error {
    fn from(e: OpError) -> Self {
        Error::Read(e)
    }
}

#[cfg(not(charon))]
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Read(e) => write!(f, "malformed encoding: {:?}", e),
            Error::InvalidMagic => write!(f, "invalid magic number"),
            Error::InvalidVersion => write!(f, "invalid version"),
            Error::UnexpectedEof => write!(f, "unexpected end of input"),
            Error::InvalidType(b) => write!(f, "invalid type byte: 0x{:02x}", b),
            Error::UnknownSection(id) => write!(f, "unknown section id: {}", id),
            Error::SectionOutOfOrder => write!(f, "section out of order"),
            Error::SectionSizeMismatch => write!(f, "section size does not match its contents"),
            Error::FuncCodeMismatch => {
                write!(f, "function and code sections have inconsistent lengths")
            }
            Error::MissingCodeSection => {
                write!(f, "the module declares functions and has no code section")
            }
            Error::InvalidUtf8 => write!(f, "name is not valid UTF-8"),
            Error::UnknownType(i) => write!(f, "unknown type: {}", i),
            Error::UnknownFunc(i) => write!(f, "unknown function: {}", i),
            Error::UnknownTable(i) => write!(f, "unknown table: {}", i),
            Error::UnknownMemory(i) => write!(f, "unknown memory: {}", i),
            Error::UnknownGlobal(i) => write!(f, "unknown global: {}", i),
            Error::DuplicateExportName => write!(f, "duplicate export name"),
            Error::LimitsOutOfRange => write!(f, "limits out of range"),
            Error::MultipleMemories => write!(f, "multiple memories"),
            Error::MultipleTables => write!(f, "multiple tables"),
            Error::InvalidStartType => write!(f, "start function must have type [] -> []"),
            Error::MutableGlobalInConstExpr => {
                write!(f, "mutable or non-imported global in constant expression")
            }
            Error::InvalidConstExpr => write!(f, "invalid constant expression"),
            Error::TooManyResults => write!(f, "a function type returns more than one value"),
            Error::TooManyLocals => write!(f, "too many locals"),
            Error::ModuleTooLarge => write!(f, "module too large"),
            Error::Body(e) => write!(f, "invalid function body: {:?}", e),
            Error::Visitor(e) => write!(f, "the consumer declined: {:?}", e),
        }
    }
}
