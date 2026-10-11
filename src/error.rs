//! Validation and embedding errors.
//!
//! `OpError` records reader and instruction failures. `Error` adds module framing
//! and streaming protocol failures. Callback errors can reject valid input; error
//! values do not include byte positions.

#[cfg(not(charon))]
use core::fmt;

/// A byte-decoding, instruction-validation, or operator-callback error.
///
/// Error variants are diagnostic. The proofs do not specify which variant must be
/// chosen for every rejected input.
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
    StackTooLarge,
    UnknownLabel,
    UnknownLocal,
    UnknownGlobal,
    ImmutableGlobal,
    UnknownMemory,
    UnknownFunc,
    UnknownType,
    UnknownTable,
    UnknownData,
    UnknownElement,
    /// A function signature exceeds the selected profile's result limit.
    TooManyResults,
    TooManyParams,
    /// An instruction's reserved zero byte is nonzero.
    ReservedByteNotZero,
    InvalidAlignment,
    /// A SIMD lane or shuffle selector is out of range.
    InvalidLane,
    TrailingBytes,
    BodyTooLarge,
    /// An operator callback rejected the input, which may otherwise be valid.
    Visitor(VisitError),
}

/// An error reported by a consumer callback.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub enum VisitError {
    OutOfMemory,
}

/// A module-decoding, validation, callback, or streaming-protocol error.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub enum Error {
    // --- The shape of the binary ---
    /// A byte read failed while decoding module structure.
    Read(OpError),
    InvalidMagic,
    InvalidVersion,
    UnexpectedEof,
    /// A type tag, limits flag, or import/export kind is unsupported.
    InvalidType(u8),
    /// A section ID is unsupported at its position in the module.
    UnknownSection(u8),
    SectionOutOfOrder,
    /// A section did not consume exactly its declared byte extent.
    SectionSizeMismatch,
    /// The function and code sections declare different function counts.
    FuncCodeMismatch,
    /// The data count differs from the number of data segments.
    DataCountMismatch,
    /// Defined functions have no corresponding code section.
    MissingCodeSection,
    /// A name contains invalid UTF-8.
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
    /// A Wasm 1.0 function type declares more than one result.
    TooManyResults,
    TooManyLocals,
    ModuleTooLarge,
    /// A function body failed validation or an operator callback rejected it.
    Body(OpError),
    /// A module callback rejected the input, which may otherwise be valid.
    Visitor(VisitError),
    /// A source or scheduler violated the streaming protocol.
    ///
    /// Examples include inconsistent region framing, zero batch settings, or a
    /// returned batch that is foreign, duplicate, or unfinished. This error does
    /// not classify Wasm validity.
    Host,
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
            Error::DataCountMismatch => write!(f, "data count does not match data segments"),
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
            Error::Host => write!(f, "the streaming host broke the driver's protocol"),
        }
    }
}
