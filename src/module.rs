//! Module metadata and internal environment, entry, and tail validation.
//!
//! The streaming driver composes these components. `validate_module` supplies its
//! contiguous source and synchronous worker. Section parsers carry declared end
//! positions and require exact consumption before accepting each section.

use alloc::vec::Vec;

use crate::code::{
    self, Context, EmptyOpVisitor, OpVisitor, VisitResult, OP_END, OP_F32_CONST, OP_F64_CONST,
    OP_GLOBAL_GET, OP_I32_CONST, OP_I64_CONST,
};
use crate::error::{Error, OpError};
use crate::limits::{
    validate_limits, MAX_LOCALS, MAX_MEMORIES, MAX_MEMORY_PAGES, MAX_RESULTS, MAX_TABLES,
    MAX_TABLE_ELEMS,
};
use crate::reader::{
    read_byte, read_f32_bits, read_f64_bits, read_s32_leb, read_s64_leb, read_u32_leb,
};
use crate::types::{
    ConstExpr, CustomSection, ElemType, ExternType, FuncType, GlobalType, Limits, MemType, Mut,
    TableType, ValueType,
};
use crate::ValidationProfile;

type Result<T> = core::result::Result<T, Error>;

const SECTION_CUSTOM: u8 = 0;
const SECTION_TYPE: u8 = 1;
const SECTION_IMPORT: u8 = 2;
const SECTION_FUNCTION: u8 = 3;
const SECTION_TABLE: u8 = 4;
const SECTION_MEMORY: u8 = 5;
const SECTION_GLOBAL: u8 = 6;
const SECTION_EXPORT: u8 = 7;
const SECTION_START: u8 = 8;
const SECTION_ELEMENT: u8 = 9;
pub(crate) const SECTION_CODE: u8 = 10;
const SECTION_DATA: u8 = 11;

// --- The environment: everything before the code section ---

/// A defined global and its initializer.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub struct Global {
    pub gtype: GlobalType,
    pub init: ConstExpr,
}

/// The declared type or type index of an import.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub enum ImportDesc {
    Func(u32),
    Table(TableType),
    Memory(MemType),
    Global(GlobalType),
}

/// An import declaration with UTF-8 module and field names stored as bytes.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone)]
pub struct Import {
    pub module: Vec<u8>,
    pub name: Vec<u8>,
    pub desc: ImportDesc,
}

/// An exported index in the corresponding module index space.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub enum ExportDesc {
    Func(u32),
    Table(u32),
    Memory(u32),
    Global(u32),
}

/// An export declaration with its UTF-8 name stored as bytes.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone)]
pub struct Export {
    pub name: Vec<u8>,
    pub desc: ExportDesc,
}

/// An active element segment with its table index, offset, and function indices.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone)]
pub struct Element {
    pub table_idx: u32,
    pub offset: ConstExpr,
    pub init: Vec<u32>,
}

/// Read-only declarations and index spaces decoded before the code section.
///
/// Streaming callers allocate storage with `Env::new`. The driver replaces it
/// before issuing batches. Metadata observed before the driver succeeds does not
/// certify a complete module.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone)]
pub struct Env {
    /// The declared function types, in type-index order.
    pub(crate) types: Vec<FuncType>,
    /// The import declarations, in binary order.
    pub(crate) imports: Vec<Import>,
    /// The defined globals and their initializers.
    pub(crate) globals: Vec<Global>,
    /// The export declarations, in binary order.
    pub(crate) exports: Vec<Export>,
    /// The active element segments.
    pub(crate) elements: Vec<Element>,
    /// The optional start-function index.
    pub(crate) start: Option<u32>,
    /// The type index of each defined function, in code-section order.
    pub(crate) func_type_indices: Vec<u32>,

    /// The function index space, with imports preceding definitions.
    pub(crate) func_types: Vec<FuncType>,
    pub(crate) table_types: Vec<TableType>,
    pub(crate) mem_types: Vec<MemType>,
    pub(crate) global_types: Vec<GlobalType>,

    /// The number of imported functions preceding defined functions.
    pub(crate) num_imported_funcs: usize,
    pub(crate) num_imported_globals: usize,
}

impl Env {
    /// Creates empty output storage for `validate_streaming`.
    ///
    /// The driver fills this storage with the decoded environment. An empty or
    /// partially validated environment is not evidence of whole-module
    /// acceptance.
    #[allow(clippy::new_without_default)]
    pub fn new() -> Env {
        Env {
            types: Vec::new(),
            imports: Vec::new(),
            globals: Vec::new(),
            exports: Vec::new(),
            elements: Vec::new(),
            start: None,
            func_type_indices: Vec::new(),
            func_types: Vec::new(),
            table_types: Vec::new(),
            mem_types: Vec::new(),
            global_types: Vec::new(),
            num_imported_funcs: 0,
            num_imported_globals: 0,
        }
    }

    /// Returns the declared function types in type-index order.
    pub fn types(&self) -> &[FuncType] {
        &self.types
    }

    /// Returns the import declarations in binary order.
    pub fn imports(&self) -> &[Import] {
        &self.imports
    }

    /// Returns the defined globals and their initializers.
    pub fn globals(&self) -> &[Global] {
        &self.globals
    }

    /// Returns the export declarations in binary order.
    pub fn exports(&self) -> &[Export] {
        &self.exports
    }

    /// Returns the active element segments.
    pub fn elements(&self) -> &[Element] {
        &self.elements
    }

    /// Returns the optional start-function index.
    pub fn start(&self) -> Option<u32> {
        self.start
    }

    /// Returns the type index of each defined function in code-section order.
    pub fn func_type_indices(&self) -> &[u32] {
        &self.func_type_indices
    }

    /// Returns the function index space, with imports preceding definitions.
    pub fn func_types(&self) -> &[FuncType] {
        &self.func_types
    }

    /// Returns the table index space, with imports preceding definitions.
    pub fn table_types(&self) -> &[TableType] {
        &self.table_types
    }

    /// Returns the memory index space, with imports preceding definitions.
    pub fn mem_types(&self) -> &[MemType] {
        &self.mem_types
    }

    /// Returns the global index space, with imports preceding definitions.
    pub fn global_types(&self) -> &[GlobalType] {
        &self.global_types
    }

    /// Returns the number of imported functions.
    pub fn num_imported_funcs(&self) -> usize {
        self.num_imported_funcs
    }

    /// Returns the number of imported globals.
    pub fn num_imported_globals(&self) -> usize {
        self.num_imported_globals
    }
}

/// An active data segment with its memory index, offset, and initialization
/// bytes.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
pub struct Data {
    pub memory_idx: u32,
    pub offset: ConstExpr,
    pub init: Vec<u8>,
}

/// The data segments decoded after the code section.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
pub struct Tail {
    pub data: Vec<Data>,
}

/// Read-only metadata returned after successful whole-module validation.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
pub struct Module {
    pub(crate) env: Env,
    pub(crate) tail: Tail,
}

impl Module {
    /// Returns the validated declarations and index spaces.
    pub fn env(&self) -> &Env {
        &self.env
    }

    /// Returns the validated data segments.
    pub fn tail(&self) -> &Tail {
        &self.tail
    }
}

/// Validates a complete module under the selected profile and returns its
/// metadata.
///
/// Accepts arbitrary bytes with no caller preconditions. Both profiles have
/// termination, soundness, and completeness guarantees within the implementation
/// limits, assuming allocation succeeds. `ValidationProfile::MultiValue` enables
/// the supported extension subset.
pub fn validate_module(data: &[u8], profile: ValidationProfile) -> Result<Module> {
    crate::stream::validate_module_slice(data, profile)
}

// --- The module's external types ---

/// Resolves import types in declaration order.
///
/// For an environment returned by successful module validation, every type index
/// is valid and resolution succeeds.
pub fn import_types(env: &Env) -> Result<Vec<ExternType>> {
    let mut out: Vec<ExternType> = Vec::new();
    let mut i: usize = 0;
    loop {
        if i >= env.imports.len() {
            return Ok(out);
        }
        let desc = env.imports[i].desc;
        match desc {
            ImportDesc::Func(idx) => {
                let ft = lookup_type(env, idx)?;
                out.push(ExternType::Func(ft));
            }
            ImportDesc::Table(tt) => out.push(ExternType::Table(tt)),
            ImportDesc::Memory(mt) => out.push(ExternType::Memory(mt)),
            ImportDesc::Global(gt) => out.push(ExternType::Global(gt)),
        }
        i += 1;
    }
}

/// Resolves export types in declaration order.
///
/// For an environment returned by successful module validation, every exported
/// index is valid and resolution succeeds.
pub fn export_types(env: &Env) -> Result<Vec<ExternType>> {
    let mut out: Vec<ExternType> = Vec::new();
    let mut i: usize = 0;
    loop {
        if i >= env.exports.len() {
            return Ok(out);
        }
        let desc = env.exports[i].desc;
        match desc {
            ExportDesc::Func(idx) => {
                let j = idx as usize;
                if j >= env.func_types.len() {
                    return Err(Error::UnknownFunc(idx));
                }
                out.push(ExternType::Func(copy_func_type(&env.func_types[j])));
            }
            ExportDesc::Table(idx) => {
                let j = idx as usize;
                if j >= env.table_types.len() {
                    return Err(Error::UnknownTable(idx));
                }
                out.push(ExternType::Table(env.table_types[j]));
            }
            ExportDesc::Memory(idx) => {
                let j = idx as usize;
                if j >= env.mem_types.len() {
                    return Err(Error::UnknownMemory(idx));
                }
                out.push(ExternType::Memory(env.mem_types[j]));
            }
            ExportDesc::Global(idx) => {
                let j = idx as usize;
                if j >= env.global_types.len() {
                    return Err(Error::UnknownGlobal(idx));
                }
                out.push(ExternType::Global(env.global_types[j]));
            }
        }
        i += 1;
    }
}

// --- Cursor helpers ---

/// Copies `data[from..to]` using the extraction-compatible byte loop.
pub(crate) fn copy_bytes(data: &[u8], from: usize, to: usize) -> Vec<u8> {
    let mut out = Vec::new();
    let mut i: usize = from;
    loop {
        if i >= to {
            return out;
        }
        out.push(data[i]);
        i += 1;
    }
}

/// Checks that `n` bytes are available at `pos` without overflowing the offset.
pub(crate) fn have_bytes(data: &[u8], pos: usize, n: usize) -> Result<()> {
    if n > data.len() - pos {
        return Err(Error::UnexpectedEof);
    }
    Ok(())
}

// --- Header and section framing ---

/// Checks the module magic and version and returns the first section position.
pub(crate) fn read_header(data: &[u8]) -> Result<usize> {
    let (m0, p1) = read_byte(data, 0)?;
    let (m1, p2) = read_byte(data, p1)?;
    let (m2, p3) = read_byte(data, p2)?;
    let (m3, p4) = read_byte(data, p3)?;
    if m0 != 0x00 || m1 != 0x61 || m2 != 0x73 || m3 != 0x6d {
        return Err(Error::InvalidMagic);
    }
    let (v0, p5) = read_byte(data, p4)?;
    let (v1, p6) = read_byte(data, p5)?;
    let (v2, p7) = read_byte(data, p6)?;
    let (v3, p8) = read_byte(data, p7)?;
    if v0 != 0x01 || v1 != 0x00 || v2 != 0x00 || v3 != 0x00 {
        return Err(Error::InvalidVersion);
    }
    Ok(p8)
}

/// Reads a section's ID and byte extent, checking that its declared contents
/// exist.
pub(crate) fn read_section_header(data: &[u8], pos: usize) -> Result<(u8, usize, usize)> {
    let (id, p) = read_byte(data, pos)?;
    let (size, q) = read_u32_leb(data, p)?;
    let n = size as usize;
    have_bytes(data, q, n)?;
    Ok((id, q, q + n))
}

// --- Types (spec 5.3) ---

pub(crate) fn decode_value_type(data: &[u8], pos: usize) -> Result<(ValueType, usize)> {
    let (b, p) = read_byte(data, pos)?;
    match b {
        0x7f => Ok((ValueType::I32, p)),
        0x7e => Ok((ValueType::I64, p)),
        0x7d => Ok((ValueType::F32, p)),
        0x7c => Ok((ValueType::F64, p)),
        _ => Err(Error::InvalidType(b)),
    }
}

fn decode_value_types(
    data: &[u8],
    pos: usize,
    bound: Option<(usize, OpError)>,
) -> Result<(Vec<ValueType>, usize)> {
    let (count, p) = read_u32_leb(data, pos)?;
    if let Some((limit, error)) = bound {
        if count as usize > limit {
            return Err(Error::Read(error));
        }
    }
    let mut out = Vec::new();
    let mut q = p;
    let mut i: u32 = 0;
    loop {
        if i >= count {
            return Ok((out, q));
        }
        let (vt, q1) = decode_value_type(data, q)?;
        out.push(vt);
        q = q1;
        i += 1;
    }
}

/// Decodes a function type and enforces the selected profile's signature limits.
fn decode_func_type(
    data: &[u8],
    pos: usize,
    profile: ValidationProfile,
) -> Result<(FuncType, usize)> {
    let (tag, p) = read_byte(data, pos)?;
    if tag != 0x60 {
        return Err(Error::InvalidType(tag));
    }
    let (params_bound, results_bound) = match profile {
        ValidationProfile::Wasm1 => (None, None),
        ValidationProfile::MultiValue => (
            Some((
                crate::limits::MAX_MULTI_VALUE_PARAMS,
                OpError::TooManyParams,
            )),
            Some((
                crate::limits::MAX_MULTI_VALUE_RESULTS,
                OpError::TooManyResults,
            )),
        ),
    };
    let (params, p1) = decode_value_types(data, p, params_bound)?;
    let (results, p2) = decode_value_types(data, p1, results_bound)?;
    match profile {
        ValidationProfile::Wasm1 => {
            if results.len() > MAX_RESULTS {
                return Err(Error::TooManyResults);
            }
        }
        ValidationProfile::MultiValue => {}
    }
    Ok((FuncType { params, results }, p2))
}

/// Decodes minimum and optional maximum limits.
fn decode_limits(data: &[u8], pos: usize) -> Result<(Limits, usize)> {
    let (flag, p) = read_byte(data, pos)?;
    match flag {
        0x00 => {
            let (min, p1) = read_u32_leb(data, p)?;
            Ok((Limits { min, max: None }, p1))
        }
        0x01 => {
            let (min, p1) = read_u32_leb(data, p)?;
            let (max, p2) = read_u32_leb(data, p1)?;
            Ok((
                Limits {
                    min,
                    max: Some(max),
                },
                p2,
            ))
        }
        _ => Err(Error::InvalidType(flag)),
    }
}

/// Decodes a funcref table type and checks its size limits.
fn decode_table_type(data: &[u8], pos: usize) -> Result<(TableType, usize)> {
    let (elem, p) = read_byte(data, pos)?;
    if elem != 0x70 {
        return Err(Error::InvalidType(elem));
    }
    let (limits, p1) = decode_limits(data, p)?;
    validate_limits(&limits, MAX_TABLE_ELEMS)?;
    Ok((
        TableType {
            limits,
            elem: ElemType::FuncRef,
        },
        p1,
    ))
}

/// Decodes a memory type and checks its page limits.
fn decode_mem_type(data: &[u8], pos: usize) -> Result<(MemType, usize)> {
    let (limits, p) = decode_limits(data, pos)?;
    validate_limits(&limits, MAX_MEMORY_PAGES)?;
    Ok((MemType { limits }, p))
}

/// Decodes a global's value type and mutability.
fn decode_global_type(data: &[u8], pos: usize) -> Result<(GlobalType, usize)> {
    let (valtype, p) = decode_value_type(data, pos)?;
    let (m, p1) = read_byte(data, p)?;
    match m {
        0x00 => Ok((
            GlobalType {
                mutability: Mut::Const,
                valtype,
            },
            p1,
        )),
        0x01 => Ok((
            GlobalType {
                mutability: Mut::Var,
                valtype,
            },
            p1,
        )),
        _ => Err(Error::InvalidType(m)),
    }
}

// --- Names (spec 5.2.4) ---

/// Checks a UTF-8 continuation byte against the required interval.
fn utf8_cont(bytes: &[u8], i: usize, lo: u8, hi: u8) -> Result<()> {
    if i >= bytes.len() {
        return Err(Error::InvalidUtf8);
    }
    let b = bytes[i];
    if b < lo || b > hi {
        return Err(Error::InvalidUtf8);
    }
    Ok(())
}

/// Checks one Unicode scalar encoding and returns its byte length.
fn utf8_sequence_len(bytes: &[u8], i: usize) -> Result<usize> {
    let b = bytes[i];
    match b {
        0xe0 => {
            utf8_cont(bytes, i + 1, 0xa0, 0xbf)?;
            utf8_cont(bytes, i + 2, 0x80, 0xbf)?;
            Ok(3)
        }
        0xed => {
            utf8_cont(bytes, i + 1, 0x80, 0x9f)?;
            utf8_cont(bytes, i + 2, 0x80, 0xbf)?;
            Ok(3)
        }
        0xf0 => {
            utf8_cont(bytes, i + 1, 0x90, 0xbf)?;
            utf8_cont(bytes, i + 2, 0x80, 0xbf)?;
            utf8_cont(bytes, i + 3, 0x80, 0xbf)?;
            Ok(4)
        }
        0xf4 => {
            utf8_cont(bytes, i + 1, 0x80, 0x8f)?;
            utf8_cont(bytes, i + 2, 0x80, 0xbf)?;
            utf8_cont(bytes, i + 3, 0x80, 0xbf)?;
            Ok(4)
        }
        ..=0x7f => Ok(1),
        0xc2..=0xdf => {
            utf8_cont(bytes, i + 1, 0x80, 0xbf)?;
            Ok(2)
        }
        0xe1..=0xef => {
            utf8_cont(bytes, i + 1, 0x80, 0xbf)?;
            utf8_cont(bytes, i + 2, 0x80, 0xbf)?;
            Ok(3)
        }
        0xf1..=0xf3 => {
            utf8_cont(bytes, i + 1, 0x80, 0xbf)?;
            utf8_cont(bytes, i + 2, 0x80, 0xbf)?;
            utf8_cont(bytes, i + 3, 0x80, 0xbf)?;
            Ok(4)
        }
        _ => Err(Error::InvalidUtf8),
    }
}

fn validate_utf8(bytes: &[u8]) -> Result<()> {
    let mut i: usize = 0;
    loop {
        if i >= bytes.len() {
            return Ok(());
        }
        let n = utf8_sequence_len(bytes, i)?;
        i += n;
    }
}

/// Decodes a length-prefixed name and checks strict UTF-8 validity.
fn decode_name(data: &[u8], pos: usize) -> Result<(Vec<u8>, usize)> {
    let (len, p) = read_u32_leb(data, pos)?;
    let n = len as usize;
    have_bytes(data, p, n)?;
    let bytes = copy_bytes(data, p, p + n);
    validate_utf8(&bytes)?;
    Ok((bytes, p + n))
}

/// Checks a custom section's name and returns its name and payload bounds.
pub(crate) fn decode_custom_section(data: &[u8], pos: usize, end: usize) -> Result<CustomSection> {
    let (name, p) = decode_name(data, pos)?;
    if p > end {
        return Err(Error::SectionSizeMismatch);
    }
    Ok(CustomSection {
        name_len: name.len(),
        payload_start: p,
        payload_end: end,
    })
}

// --- Constant expressions (spec 5.4.1, restricted by 3.4.10) ---

fn expect_const_type(actual: ValueType, expected: ValueType) -> Result<()> {
    if actual != expected {
        return Err(Error::InvalidConstExpr);
    }
    Ok(())
}

fn read_expr_end(data: &[u8], pos: usize) -> Result<usize> {
    let (b, p) = read_byte(data, pos)?;
    if b != OP_END {
        return Err(Error::InvalidConstExpr);
    }
    Ok(p)
}

/// Resolves an immutable imported global for a constant expression.
fn const_global(env: &Env, idx: u32) -> Result<GlobalType> {
    let i = idx as usize;
    if i >= env.global_types.len() {
        return Err(Error::UnknownGlobal(idx));
    }
    if i >= env.num_imported_globals {
        return Err(Error::MutableGlobalInConstExpr);
    }
    let gt = env.global_types[i];
    if gt.mutability != Mut::Const {
        return Err(Error::MutableGlobalInConstExpr);
    }
    Ok(gt)
}

/// Decodes a single-instruction constant expression of the expected type.
pub(crate) fn decode_const_expr(
    data: &[u8],
    pos: usize,
    env: &Env,
    expected: ValueType,
) -> Result<(ConstExpr, usize)> {
    let (op, p) = read_byte(data, pos)?;
    match op {
        OP_I32_CONST => {
            let (v, p1) = read_s32_leb(data, p)?;
            expect_const_type(ValueType::I32, expected)?;
            let p2 = read_expr_end(data, p1)?;
            Ok((ConstExpr::I32(v), p2))
        }
        OP_I64_CONST => {
            let (v, p1) = read_s64_leb(data, p)?;
            expect_const_type(ValueType::I64, expected)?;
            let p2 = read_expr_end(data, p1)?;
            Ok((ConstExpr::I64(v), p2))
        }
        OP_F32_CONST => {
            let (v, p1) = read_f32_bits(data, p)?;
            expect_const_type(ValueType::F32, expected)?;
            let p2 = read_expr_end(data, p1)?;
            Ok((ConstExpr::F32(v), p2))
        }
        OP_F64_CONST => {
            let (v, p1) = read_f64_bits(data, p)?;
            expect_const_type(ValueType::F64, expected)?;
            let p2 = read_expr_end(data, p1)?;
            Ok((ConstExpr::F64(v), p2))
        }
        OP_GLOBAL_GET => {
            let (idx, p1) = read_u32_leb(data, p)?;
            let gt = const_global(env, idx)?;
            expect_const_type(gt.valtype, expected)?;
            let p2 = read_expr_end(data, p1)?;
            Ok((ConstExpr::GlobalGet(idx), p2))
        }
        _ => Err(Error::InvalidConstExpr),
    }
}

// --- Copying, since no Clone impl reaches the extraction ---

fn copy_value_types(src: &[ValueType]) -> Vec<ValueType> {
    let mut out = Vec::new();
    let mut i: usize = 0;
    loop {
        if i >= src.len() {
            return out;
        }
        out.push(src[i]);
        i += 1;
    }
}

fn copy_func_type(ft: &FuncType) -> FuncType {
    FuncType {
        params: copy_value_types(&ft.params),
        results: copy_value_types(&ft.results),
    }
}

/// Checks a function type index and copies its signature.
fn lookup_type(env: &Env, idx: u32) -> Result<FuncType> {
    let i = idx as usize;
    if i >= env.types.len() {
        return Err(Error::UnknownType(idx));
    }
    Ok(copy_func_type(&env.types[i]))
}

// --- The environment's sections ---

fn decode_type_section(
    data: &[u8],
    pos: usize,
    env: &mut Env,
    profile: ValidationProfile,
) -> Result<usize> {
    let (count, p) = read_u32_leb(data, pos)?;
    let mut q = p;
    let mut i: u32 = 0;
    loop {
        if i >= count {
            return Ok(q);
        }
        let (ft, q1) = decode_func_type(data, q, profile)?;
        env.types.push(ft);
        q = q1;
        i += 1;
    }
}

/// Decodes an import and appends it to the corresponding index space.
fn decode_import(data: &[u8], pos: usize, env: &mut Env) -> Result<usize> {
    let (module, p1) = decode_name(data, pos)?;
    let (name, p2) = decode_name(data, p1)?;
    let (kind, p3) = read_byte(data, p2)?;
    match kind {
        0x00 => {
            let (idx, p4) = read_u32_leb(data, p3)?;
            let ft = lookup_type(env, idx)?;
            env.func_types.push(ft);
            env.num_imported_funcs += 1;
            env.imports.push(Import {
                module,
                name,
                desc: ImportDesc::Func(idx),
            });
            Ok(p4)
        }
        0x01 => {
            let (tt, p4) = decode_table_type(data, p3)?;
            env.table_types.push(tt);
            if env.table_types.len() > MAX_TABLES {
                return Err(Error::MultipleTables);
            }
            env.imports.push(Import {
                module,
                name,
                desc: ImportDesc::Table(tt),
            });
            Ok(p4)
        }
        0x02 => {
            let (mt, p4) = decode_mem_type(data, p3)?;
            env.mem_types.push(mt);
            if env.mem_types.len() > MAX_MEMORIES {
                return Err(Error::MultipleMemories);
            }
            env.imports.push(Import {
                module,
                name,
                desc: ImportDesc::Memory(mt),
            });
            Ok(p4)
        }
        0x03 => {
            let (gt, p4) = decode_global_type(data, p3)?;
            env.global_types.push(gt);
            env.num_imported_globals += 1;
            env.imports.push(Import {
                module,
                name,
                desc: ImportDesc::Global(gt),
            });
            Ok(p4)
        }
        _ => Err(Error::InvalidType(kind)),
    }
}

fn decode_import_section(data: &[u8], pos: usize, env: &mut Env) -> Result<usize> {
    let (count, p) = read_u32_leb(data, pos)?;
    let mut q = p;
    let mut i: u32 = 0;
    loop {
        if i >= count {
            return Ok(q);
        }
        q = decode_import(data, q, env)?;
        i += 1;
    }
}

fn decode_function_section(data: &[u8], pos: usize, env: &mut Env) -> Result<usize> {
    let (count, p) = read_u32_leb(data, pos)?;
    let mut q = p;
    let mut i: u32 = 0;
    loop {
        if i >= count {
            return Ok(q);
        }
        let (idx, q1) = read_u32_leb(data, q)?;
        let ft = lookup_type(env, idx)?;
        env.func_types.push(ft);
        env.func_type_indices.push(idx);
        q = q1;
        i += 1;
    }
}

fn decode_table_section(data: &[u8], pos: usize, env: &mut Env) -> Result<usize> {
    let (count, p) = read_u32_leb(data, pos)?;
    let mut q = p;
    let mut i: u32 = 0;
    loop {
        if i >= count {
            return Ok(q);
        }
        let (tt, q1) = decode_table_type(data, q)?;
        env.table_types.push(tt);
        if env.table_types.len() > MAX_TABLES {
            return Err(Error::MultipleTables);
        }
        q = q1;
        i += 1;
    }
}

fn decode_memory_section(data: &[u8], pos: usize, env: &mut Env) -> Result<usize> {
    let (count, p) = read_u32_leb(data, pos)?;
    let mut q = p;
    let mut i: u32 = 0;
    loop {
        if i >= count {
            return Ok(q);
        }
        let (mt, q1) = decode_mem_type(data, q)?;
        env.mem_types.push(mt);
        if env.mem_types.len() > MAX_MEMORIES {
            return Err(Error::MultipleMemories);
        }
        q = q1;
        i += 1;
    }
}

fn decode_global_section(data: &[u8], pos: usize, env: &mut Env) -> Result<usize> {
    let (count, p) = read_u32_leb(data, pos)?;
    let mut q = p;
    let mut i: u32 = 0;
    loop {
        if i >= count {
            return Ok(q);
        }
        let (gtype, q1) = decode_global_type(data, q)?;
        let (init, q2) = decode_const_expr(data, q1, env, gtype.valtype)?;
        env.global_types.push(gtype);
        env.globals.push(Global { gtype, init });
        q = q2;
        i += 1;
    }
}

fn names_equal(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    loop {
        if i >= a.len() {
            return true;
        }
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
}

/// Returns whether an earlier export has the same decoded name bytes.
fn export_name_taken(env: &Env, name: &[u8]) -> bool {
    let mut i: usize = 0;
    loop {
        if i >= env.exports.len() {
            return false;
        }
        if names_equal(&env.exports[i].name, name) {
            return true;
        }
        i += 1;
    }
}

fn export_desc(env: &Env, kind: u8, idx: u32) -> Result<ExportDesc> {
    let i = idx as usize;
    match kind {
        0x00 => {
            if i >= env.func_types.len() {
                return Err(Error::UnknownFunc(idx));
            }
            Ok(ExportDesc::Func(idx))
        }
        0x01 => {
            if i >= env.table_types.len() {
                return Err(Error::UnknownTable(idx));
            }
            Ok(ExportDesc::Table(idx))
        }
        0x02 => {
            if i >= env.mem_types.len() {
                return Err(Error::UnknownMemory(idx));
            }
            Ok(ExportDesc::Memory(idx))
        }
        0x03 => {
            if i >= env.global_types.len() {
                return Err(Error::UnknownGlobal(idx));
            }
            Ok(ExportDesc::Global(idx))
        }
        _ => Err(Error::InvalidType(kind)),
    }
}

fn decode_export_section(data: &[u8], pos: usize, env: &mut Env) -> Result<usize> {
    let (count, p) = read_u32_leb(data, pos)?;
    let mut q = p;
    let mut i: u32 = 0;
    loop {
        if i >= count {
            return Ok(q);
        }
        let (name, q1) = decode_name(data, q)?;
        if export_name_taken(env, &name) {
            return Err(Error::DuplicateExportName);
        }
        let (kind, q2) = read_byte(data, q1)?;
        let (idx, q3) = read_u32_leb(data, q2)?;
        let desc = export_desc(env, kind, idx)?;
        env.exports.push(Export { name, desc });
        q = q3;
        i += 1;
    }
}

/// Decodes the start-function index and requires an empty parameter and result
/// signature.
fn decode_start_section(data: &[u8], pos: usize, env: &mut Env) -> Result<usize> {
    let (idx, p) = read_u32_leb(data, pos)?;
    let i = idx as usize;
    if i >= env.func_types.len() {
        return Err(Error::UnknownFunc(idx));
    }
    if !env.func_types[i].params.is_empty() || !env.func_types[i].results.is_empty() {
        return Err(Error::InvalidStartType);
    }
    env.start = Some(idx);
    Ok(p)
}

pub(crate) fn decode_func_indices(data: &[u8], pos: usize, env: &Env) -> Result<(Vec<u32>, usize)> {
    let (count, p) = read_u32_leb(data, pos)?;
    let mut out = Vec::new();
    let mut q = p;
    let mut i: u32 = 0;
    loop {
        if i >= count {
            return Ok((out, q));
        }
        let (idx, q1) = read_u32_leb(data, q)?;
        if idx as usize >= env.func_types.len() {
            return Err(Error::UnknownFunc(idx));
        }
        out.push(idx);
        q = q1;
        i += 1;
    }
}

/// Decodes a Wasm 1.0 segment index or multi-value active-segment flags.
fn decode_segment_index(
    data: &[u8],
    pos: usize,
    index_or_flags: u32,
    profile: ValidationProfile,
) -> Result<(u32, usize, bool)> {
    match profile {
        ValidationProfile::Wasm1 => Ok((index_or_flags, pos, false)),
        ValidationProfile::MultiValue => match index_or_flags {
            0 => Ok((0, pos, false)),
            2 => {
                let (index, next) = read_u32_leb(data, pos)?;
                Ok((index, next, true))
            }
            _ => Err(Error::InvalidType(0xff)),
        },
    }
}

fn decode_element_section(
    data: &[u8],
    pos: usize,
    env: &mut Env,
    profile: ValidationProfile,
) -> Result<usize> {
    let (count, p) = read_u32_leb(data, pos)?;
    let mut q = p;
    let mut i: u32 = 0;
    loop {
        if i >= count {
            return Ok(q);
        }
        let (index_or_flags, q1) = read_u32_leb(data, q)?;
        let (table_idx, q1, explicit) = decode_segment_index(data, q1, index_or_flags, profile)?;
        if table_idx as usize >= env.table_types.len() {
            return Err(Error::UnknownTable(table_idx));
        }
        let (offset, mut q2) = decode_const_expr(data, q1, env, ValueType::I32)?;
        if explicit {
            let (kind, next) = read_byte(data, q2)?;
            if kind != 0 {
                return Err(Error::InvalidType(kind));
            }
            q2 = next;
        }
        let (init, q3) = decode_func_indices(data, q2, env)?;
        env.elements.push(Element {
            table_idx,
            offset,
            init,
        });
        q = q3;
        i += 1;
    }
}

pub(crate) fn decode_env_section(
    data: &[u8],
    pos: usize,
    id: u8,
    env: &mut Env,
    profile: ValidationProfile,
) -> Result<usize> {
    match id {
        SECTION_TYPE => decode_type_section(data, pos, env, profile),
        SECTION_IMPORT => decode_import_section(data, pos, env),
        SECTION_FUNCTION => decode_function_section(data, pos, env),
        SECTION_TABLE => decode_table_section(data, pos, env),
        SECTION_MEMORY => decode_memory_section(data, pos, env),
        SECTION_GLOBAL => decode_global_section(data, pos, env),
        SECTION_EXPORT => decode_export_section(data, pos, env),
        SECTION_START => decode_start_section(data, pos, env),
        SECTION_ELEMENT => decode_element_section(data, pos, env, profile),
        _ => Err(Error::UnknownSection(id)),
    }
}

/// Validates the environment with accepting custom-section callbacks.
#[allow(dead_code)] // Retained as an extracted proof entry point.
pub(crate) fn validate_env(data: &[u8], profile: ValidationProfile) -> Result<(Env, usize)> {
    let mut nop = EmptyModuleVisitor;
    validate_env_with(data, profile, &mut nop)
}

/// Decodes the declarations before the code section and reports custom sections.
///
/// Returns the environment and the next section position. The caller must bound
/// `data` by `MAX_MODULE_BYTES`; the streaming driver establishes this bound.
pub(crate) fn validate_env_with<V: ModuleVisitor>(
    data: &[u8],
    profile: ValidationProfile,
    v: &mut V,
) -> Result<(Env, usize)> {
    let mut env = Env::new();
    let mut q = read_header(data)?;
    let mut last_id: u8 = 0;
    loop {
        if q >= data.len() {
            return Ok((env, q));
        }
        let (id, start, end) = read_section_header(data, q)?;
        if id == SECTION_CUSTOM {
            let c = decode_custom_section(data, start, end)?;
            match v.on_custom_section(c) {
                Ok(()) => {}
                Err(e) => return Err(Error::Visitor(e)),
            }
            q = end;
        } else if id >= SECTION_CODE {
            // The code section and everything after it belong to the other two
            // parts, so hand back the header unread.
            return Ok((env, q));
        } else if id <= last_id {
            return Err(Error::SectionOutOfOrder);
        } else {
            last_id = id;
            let p = decode_env_section(data, start, id, &mut env, profile)?;
            if p != end {
                return Err(Error::SectionSizeMismatch);
            }
            q = end;
        }
    }
}

// --- The code section ---

fn push_locals(out: &mut Vec<ValueType>, count: u32, vt: ValueType) {
    let mut i: u32 = 0;
    loop {
        if i >= count {
            return;
        }
        out.push(vt);
        i += 1;
    }
}

/// Decodes grouped local declarations, enforcing the declared-local limit before
/// expansion.
pub(crate) fn decode_locals(data: &[u8], pos: usize) -> Result<(Vec<ValueType>, usize)> {
    let (groups, p) = read_u32_leb(data, pos)?;
    let mut out = Vec::new();
    let mut q = p;
    let mut i: u32 = 0;
    loop {
        if i >= groups {
            return Ok((out, q));
        }
        let (count, q1) = read_u32_leb(data, q)?;
        let (vt, q2) = decode_value_type(data, q1)?;
        // The count is a u32 with no byte cost, so it is the one place in the
        // format where a couple of bytes can ask for an unbounded allocation.
        if count as usize > MAX_LOCALS - out.len() {
            return Err(Error::TooManyLocals);
        }
        push_locals(&mut out, count, vt);
        q = q2;
        i += 1;
    }
}

pub(crate) fn build_func_locals(params: &[ValueType], declared: &[ValueType]) -> Vec<ValueType> {
    let mut locals = copy_value_types(params);
    let mut i: usize = 0;
    loop {
        if i >= declared.len() {
            return locals;
        }
        locals.push(declared[i]);
        i += 1;
    }
}

/// Validates a framed function entry and reports its context and operators.
///
/// `pos` points to the size prefix; `index` selects the defined function in
/// `env`. The environment must come from an accepted bounded decode of the same
/// logical module and profile. The returned position is the entry end. The
/// streaming batch wrapper establishes these conditions and records the result.
pub(crate) fn validate_code_entry_with<V: OpVisitor>(
    data: &[u8],
    pos: usize,
    env: &Env,
    index: usize,
    profile: ValidationProfile,
    v: &mut V,
) -> Result<usize> {
    if index >= env.func_type_indices.len() {
        return Err(Error::FuncCodeMismatch);
    }
    let (size, p) = read_u32_leb(data, pos)?;
    let n = size as usize;
    have_bytes(data, p, n)?;
    let end = p + n;

    let (declared, p1) = decode_locals(data, p)?;
    if p1 > end {
        return Err(Error::SectionSizeMismatch);
    }

    let type_idx = env.func_type_indices[index];
    let t = type_idx as usize;
    if t >= env.types.len() {
        return Err(Error::UnknownType(type_idx));
    }
    let ctx = Context {
        locals: build_func_locals(&env.types[t].params, &declared),
        results: copy_value_types(&env.types[t].results),
    };

    // The consumer sees the frame it is about to compile before the first
    // operator of it, which is why this is a hook and not a return value.
    match v.on_function_start(&ctx, type_idx, p1, end) {
        Ok(()) => {}
        Err(e) => return Err(Error::Body(OpError::Visitor(e))),
    }

    // `validate_body_with` takes the body's own bytes and nothing else: it is
    // what decides that the last byte is the terminating `end`.
    let body_result = match profile {
        ValidationProfile::Wasm1 => code::validate_body_with(&data[p1..end], env, &ctx, v),
        ValidationProfile::MultiValue => {
            code::validate_multi_value_body_with(&data[p1..end], env, &ctx, type_idx, v)
        }
    };
    match body_result {
        Ok(()) => Ok(end),
        Err(e) => Err(Error::Body(e)),
    }
}

/// Validates a framed function entry with accepting operator callbacks.
#[allow(dead_code)] // Retained as an extracted proof entry point.
pub(crate) fn validate_code_entry(
    data: &[u8],
    pos: usize,
    env: &Env,
    index: usize,
    profile: ValidationProfile,
) -> Result<usize> {
    let mut nop = EmptyOpVisitor;
    validate_code_entry_with(data, pos, env, index, profile, &mut nop)
}

// --- The tail ---

fn decode_data_segment(
    data: &[u8],
    pos: usize,
    env: &Env,
    profile: ValidationProfile,
) -> Result<(Data, usize)> {
    let (index_or_flags, p1) = read_u32_leb(data, pos)?;
    let (memory_idx, p1, _) = decode_segment_index(data, p1, index_or_flags, profile)?;
    if memory_idx as usize >= env.mem_types.len() {
        return Err(Error::UnknownMemory(memory_idx));
    }
    let (offset, p2) = decode_const_expr(data, p1, env, ValueType::I32)?;
    let (len, p3) = read_u32_leb(data, p2)?;
    let n = len as usize;
    have_bytes(data, p3, n)?;
    let init = copy_bytes(data, p3, p3 + n);
    Ok((
        Data {
            memory_idx,
            offset,
            init,
        },
        p3 + n,
    ))
}

fn decode_data_section(
    data: &[u8],
    pos: usize,
    env: &Env,
    profile: ValidationProfile,
) -> Result<(Vec<Data>, usize)> {
    let (count, p) = read_u32_leb(data, pos)?;
    let mut out = Vec::new();
    let mut q = p;
    let mut i: u32 = 0;
    loop {
        if i >= count {
            return Ok((out, q));
        }
        let (segment, q1) = decode_data_segment(data, q, env, profile)?;
        out.push(segment);
        q = q1;
        i += 1;
    }
}

/// Validates the tail with accepting custom-section callbacks.
#[allow(dead_code)] // Retained as an extracted proof entry point.
pub(crate) fn validate_tail(
    data: &[u8],
    pos: usize,
    env: &Env,
    profile: ValidationProfile,
) -> Result<Tail> {
    let mut nop = EmptyModuleVisitor;
    validate_tail_with(data, pos, env, profile, &mut nop)
}

/// Decodes data and custom sections after the code section.
///
/// `pos` starts the tail and `env` belongs to the same logical module and
/// profile. The streaming driver checks the complete region framing separately.
pub(crate) fn validate_tail_with<V: ModuleVisitor>(
    data: &[u8],
    pos: usize,
    env: &Env,
    profile: ValidationProfile,
    v: &mut V,
) -> Result<Tail> {
    let mut segments = Vec::new();
    let mut q = pos;
    let mut seen_data = false;
    loop {
        if q >= data.len() {
            return Ok(Tail { data: segments });
        }
        let (id, start, end) = read_section_header(data, q)?;
        if id == SECTION_CUSTOM {
            let c = decode_custom_section(data, start, end)?;
            match v.on_custom_section(c) {
                Ok(()) => {}
                Err(e) => return Err(Error::Visitor(e)),
            }
            q = end;
        } else if id != SECTION_DATA || seen_data {
            return Err(Error::SectionOutOfOrder);
        } else {
            seen_data = true;
            let (decoded, p) = decode_data_section(data, start, env, profile)?;
            if p != end {
                return Err(Error::SectionSizeMismatch);
            }
            segments = decoded;
            q = end;
        }
    }
}

/// Returns the contents and end positions of a size-prefixed function entry.
pub(crate) fn code_entry_extent(data: &[u8], pos: usize) -> Result<(usize, usize)> {
    let (size, p) = read_u32_leb(data, pos)?;
    let n = size as usize;
    have_bytes(data, p, n)?;
    Ok((p, p + n))
}

/// Callbacks for custom sections during module validation.
///
/// The default hook accepts. Callback errors reject the module; termination
/// requires callbacks to return normally.
pub trait ModuleVisitor {
    /// Reports a custom section after checking its framing and UTF-8 name.
    ///
    /// Offsets refer to the current `Region` selected by the streaming
    /// visitor. Payload bytes are opaque to validation.
    fn on_custom_section(&mut self, _section: CustomSection) -> VisitResult {
        Ok(())
    }
}

/// A module visitor whose default custom-section hook accepts.
pub struct EmptyModuleVisitor;
impl ModuleVisitor for EmptyModuleVisitor {}
