//! Decode and validate a Wasm 1.0 module in a single pass.
//!
//! Three parts: the environment (`decode_env`, everything before the code
//! section), the code section (`validate_code`, one entry at a time), and the
//! tail (`decode_tail`, the data segments). The code and the tail both read
//! the environment; neither can see the other. There is no decode pass that
//! runs first: every check happens as its section is decoded, which works
//! because no check ever needs a section that comes later. A function body is
//! the exception, handed to `validate_body` as a sub-slice, because
//! `validate_body` is what decides the last byte is the terminating `end`.
//! Aeneas cannot translate a struct that holds a borrow, so sections are
//! delimited by an `end` position threaded alongside `pos` instead of a
//! sub-slice; reads are only checked against that end rather than bounded by
//! it, since `pos` only ever grows and a read past a section's end leaves
//! `pos > end`, which the equality check at the section's close rejects.

use alloc::vec::Vec;

use crate::env::{Element, Env, Export, ExportDesc, Global, Import, ImportDesc};
use crate::error::{Error, OpError};
use crate::limits::{
    validate_limits, Limits, MAX_CODE_HEADER_BYTES, MAX_LEB_BYTES, MAX_LOCALS, MAX_MEMORIES,
    MAX_MEMORY_PAGES, MAX_MODULE_BYTES, MAX_RESULTS, MAX_TABLES, MAX_TABLE_ELEMS,
};
use crate::opiter::{
    self, Context, OP_END, OP_F32_CONST, OP_F64_CONST, OP_GLOBAL_GET, OP_I32_CONST, OP_I64_CONST,
};
use crate::visit::{NopVisitor, OpVisitor, VisitResult};
use crate::reader::{
    read_byte, read_f32_bits, read_f64_bits, read_s32_leb, read_s64_leb, read_u32_leb,
};
use crate::types::{
    ConstExpr, CustomSection, ElemType, ExternType, FuncType, GlobalType, MemType, Mut, TableType,
    ValueType,
};

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
const SECTION_CODE: u8 = 10;
const SECTION_DATA: u8 = 11;

/// A data segment: a memory, an offset into it, and the bytes to write.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
pub struct Data {
    pub memory_idx: u32,
    pub offset: ConstExpr,
    pub init: Vec<u8>,
}

/// Everything after the code section. Only data segments, in Wasm 1.0.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
pub struct Tail {
    pub data: Vec<Data>,
}

/// A module that has been decoded and validated.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
pub struct ValidatedModule {
    pub env: Env,
    pub tail: Tail,
}

/// Decode and validate a Wasm 1.0 module, reporting what it passes to `v`.
///
/// The three parts in the order a module has them, driven by one consumer:
/// the custom sections before the code section, then the code section's
/// entries, then the custom sections after it. That is the whole of the
/// interface a compiler drives, in one call, for a caller that holds the
/// module in one buffer. One that holds it in pieces calls the three parts
/// itself with the same `v`, and `Module_Driven.validate_module_of_parts` says
/// that is the same run.
///
/// No precondition on `data`: the size check is here, as it is in
/// `validate_module`. What `v` is trusted for is on [`ModuleVisitor`] and
/// [`CodeVisitor`].
///
/// `Module_Driven.validate_module_with_no_panic` (given `module_hooks_total`
/// and `code_hooks_total`), `Module_Sound.validate_module_driven` and
/// `Module_Driven.validate_module_with_accepts` (given the two `_accept`
/// obligations, and `code_hooks_validate` for the first). The driven run and
/// the plain one accept the same modules and report the same
/// `ValidatedModule`, so every `validate_module` result below holds of this
/// one too.
pub fn validate_module_with<V: ModuleVisitor + CodeVisitor>(
    data: &[u8],
    v: &mut V,
) -> Result<ValidatedModule> {
    if data.len() > MAX_MODULE_BYTES {
        return Err(Error::ModuleTooLarge);
    }
    let (env, code_pos) = decode_env_with(data, v)?;
    let tail_pos = validate_code_with(data, code_pos, &env, v)?;
    let tail = decode_tail_with(data, tail_pos, &env, v)?;
    Ok(ValidatedModule { env, tail })
}

/// Decode and validate a Wasm 1.0 module.
///
/// No preconditions: any byte string at all is a legitimate argument, and the
/// size check is inside. `validate_module_no_panic` says it always returns,
/// `validate_module_repr` and `validate_module_typed` that an accepted input
/// is a well-typed Wasm 1.0 module binary, and `validate_module_complete` and
/// `validate_module_typechecked` that a valid one is not rejected.
pub fn validate_module(data: &[u8]) -> Result<ValidatedModule> {
    if data.len() > MAX_MODULE_BYTES {
        return Err(Error::ModuleTooLarge);
    }
    let (env, code_pos) = decode_env(data)?;
    let tail_pos = validate_code(data, code_pos, &env)?;
    let tail = decode_tail(data, tail_pos, &env)?;
    Ok(ValidatedModule { env, tail })
}

// --- The module's external types ---

/// The type of every import the module declares (spec 3.2.7), in declaration
/// order. This is the list an embedder matches the values it supplies against.
///
/// `env` must have come out of a whole module that validated, either
/// `validate_module` or the three parts composed. `Err` cannot happen for one
/// that did -- every import's type index was resolved as the import section
/// was decoded -- and `Module_Typing.validate_module_typed` says the list is
/// the one WebAssembly's type system assigns. For any other `Env` the result
/// is a list about no module.
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

/// The type of every export the module declares (spec 3.2.7), in declaration
/// order. An export names an index space entry, so the type comes from the
/// index space rather than from the export itself.
///
/// Same condition on `env` as [`import_types`]. `Err` cannot happen for one
/// that came out of a module that validated: `export_desc` range-checked every
/// index as the export section was decoded.
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

/// The bytes in `[from, to)`, copied out. Only for the two things a module
/// keeps: a name and a data segment's contents. A byte range that is merely
/// read, like a function body, is passed as a sub-slice instead.
fn copy_bytes(data: &[u8], from: usize, to: usize) -> Vec<u8> {
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

/// `n` bytes are available at `pos`. Written as a subtraction rather than
/// `pos + n <= data.len()` so that the sum cannot overflow.
fn have_bytes(data: &[u8], pos: usize, n: usize) -> Result<()> {
    if n > data.len() - pos {
        return Err(Error::UnexpectedEof);
    }
    Ok(())
}

// --- Header and section framing ---

/// Spec 5.5.16: the magic number and the version, eight bytes.
fn read_header(data: &[u8]) -> Result<usize> {
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

/// Spec 5.5.2: a section is an id, a byte count, and that many bytes.
/// Returns the id, where the contents start, and where they end.
fn read_section_header(data: &[u8], pos: usize) -> Result<(u8, usize, usize)> {
    let (id, p) = read_byte(data, pos)?;
    let (size, q) = read_u32_leb(data, p)?;
    let n = size as usize;
    have_bytes(data, q, n)?;
    Ok((id, q, q + n))
}

// --- Types (spec 5.3) ---

fn decode_value_type(data: &[u8], pos: usize) -> Result<(ValueType, usize)> {
    let (b, p) = read_byte(data, pos)?;
    if b == 0x7f {
        return Ok((ValueType::I32, p));
    }
    if b == 0x7e {
        return Ok((ValueType::I64, p));
    }
    if b == 0x7d {
        return Ok((ValueType::F32, p));
    }
    if b == 0x7c {
        return Ok((ValueType::F64, p));
    }
    Err(Error::InvalidType(b))
}

fn decode_value_types(data: &[u8], pos: usize) -> Result<(Vec<ValueType>, usize)> {
    let (count, p) = read_u32_leb(data, pos)?;
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

/// Spec 5.3.3. The result count is checked here rather than left to the body
/// validator: Wasm 1.0 has no multi-value, and a type that cannot be written
/// down should not decode.
fn decode_func_type(data: &[u8], pos: usize) -> Result<(FuncType, usize)> {
    let (tag, p) = read_byte(data, pos)?;
    if tag != 0x60 {
        return Err(Error::InvalidType(tag));
    }
    let (params, p1) = decode_value_types(data, p)?;
    let (results, p2) = decode_value_types(data, p1)?;
    if results.len() > MAX_RESULTS {
        return Err(Error::TooManyResults);
    }
    Ok((FuncType { params, results }, p2))
}

/// Spec 5.3.7.
fn decode_limits(data: &[u8], pos: usize) -> Result<(Limits, usize)> {
    let (flag, p) = read_byte(data, pos)?;
    if flag == 0x00 {
        let (min, p1) = read_u32_leb(data, p)?;
        return Ok((Limits { min, max: None }, p1));
    }
    if flag == 0x01 {
        let (min, p1) = read_u32_leb(data, p)?;
        let (max, p2) = read_u32_leb(data, p1)?;
        return Ok((
            Limits {
                min,
                max: Some(max),
            },
            p2,
        ));
    }
    Err(Error::InvalidType(flag))
}

/// Spec 5.3.9. `funcref` is the only element type Wasm 1.0 has.
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

/// Spec 5.3.8.
fn decode_mem_type(data: &[u8], pos: usize) -> Result<(MemType, usize)> {
    let (limits, p) = decode_limits(data, pos)?;
    validate_limits(&limits, MAX_MEMORY_PAGES)?;
    Ok((MemType { limits }, p))
}

/// Spec 5.3.10.
fn decode_global_type(data: &[u8], pos: usize) -> Result<(GlobalType, usize)> {
    let (valtype, p) = decode_value_type(data, pos)?;
    let (m, p1) = read_byte(data, p)?;
    if m == 0x00 {
        return Ok((
            GlobalType {
                mutability: Mut::Const,
                valtype,
            },
            p1,
        ));
    }
    if m == 0x01 {
        return Ok((
            GlobalType {
                mutability: Mut::Var,
                valtype,
            },
            p1,
        ));
    }
    Err(Error::InvalidType(m))
}

// --- Names (spec 5.2.4) ---

/// A continuation byte in `[lo, hi]`.
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

/// The length of the well-formed UTF-8 sequence starting at `i`, or an error.
///
/// The ranges are Unicode's well-formed byte sequence table, which is what
/// excludes overlong encodings and the surrogate range. Comparisons only: the
/// Aeneas subset has no bitwise operators.
fn utf8_sequence_len(bytes: &[u8], i: usize) -> Result<usize> {
    let b = bytes[i];
    if b <= 0x7f {
        return Ok(1);
    }
    if b >= 0xc2 && b <= 0xdf {
        utf8_cont(bytes, i + 1, 0x80, 0xbf)?;
        return Ok(2);
    }
    if b == 0xe0 {
        utf8_cont(bytes, i + 1, 0xa0, 0xbf)?;
        utf8_cont(bytes, i + 2, 0x80, 0xbf)?;
        return Ok(3);
    }
    if b == 0xed {
        utf8_cont(bytes, i + 1, 0x80, 0x9f)?;
        utf8_cont(bytes, i + 2, 0x80, 0xbf)?;
        return Ok(3);
    }
    if (b >= 0xe1 && b <= 0xec) || b == 0xee || b == 0xef {
        utf8_cont(bytes, i + 1, 0x80, 0xbf)?;
        utf8_cont(bytes, i + 2, 0x80, 0xbf)?;
        return Ok(3);
    }
    if b == 0xf0 {
        utf8_cont(bytes, i + 1, 0x90, 0xbf)?;
        utf8_cont(bytes, i + 2, 0x80, 0xbf)?;
        utf8_cont(bytes, i + 3, 0x80, 0xbf)?;
        return Ok(4);
    }
    if b == 0xf4 {
        utf8_cont(bytes, i + 1, 0x80, 0x8f)?;
        utf8_cont(bytes, i + 2, 0x80, 0xbf)?;
        utf8_cont(bytes, i + 3, 0x80, 0xbf)?;
        return Ok(4);
    }
    if b >= 0xf1 && b <= 0xf3 {
        utf8_cont(bytes, i + 1, 0x80, 0xbf)?;
        utf8_cont(bytes, i + 2, 0x80, 0xbf)?;
        utf8_cont(bytes, i + 3, 0x80, 0xbf)?;
        return Ok(4);
    }
    Err(Error::InvalidUtf8)
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

/// Spec 5.2.4: a name is a byte vector that has to be valid UTF-8.
fn decode_name(data: &[u8], pos: usize) -> Result<(Vec<u8>, usize)> {
    let (len, p) = read_u32_leb(data, pos)?;
    let n = len as usize;
    have_bytes(data, p, n)?;
    let bytes = copy_bytes(data, p, p + n);
    validate_utf8(&bytes)?;
    Ok((bytes, p + n))
}

/// Spec 5.5.3: `custom ::= nm:name b*:byte*`.
///
/// Nothing in the module a binary denotes reads the trailing bytes, but the
/// name is still a name: it has to be there, it has to be valid UTF-8, and it
/// has to fit inside the section.
///
/// What comes back is where the section is, not what its name says: the name
/// is read and checked and then dropped, and its length is what locates it.
fn decode_custom_section(data: &[u8], pos: usize, end: usize) -> Result<CustomSection> {
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

/// The global an initialiser may name: an imported one, and immutable, because
/// the globals this module defines are not initialised yet.
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

/// Decode a constant expression and check that it has the type the context
/// wants, both in one read.
fn decode_const_expr(
    data: &[u8],
    pos: usize,
    env: &Env,
    expected: ValueType,
) -> Result<(ConstExpr, usize)> {
    let (op, p) = read_byte(data, pos)?;
    if op == OP_I32_CONST {
        let (v, p1) = read_s32_leb(data, p)?;
        expect_const_type(ValueType::I32, expected)?;
        let p2 = read_expr_end(data, p1)?;
        return Ok((ConstExpr::I32(v), p2));
    }
    if op == OP_I64_CONST {
        let (v, p1) = read_s64_leb(data, p)?;
        expect_const_type(ValueType::I64, expected)?;
        let p2 = read_expr_end(data, p1)?;
        return Ok((ConstExpr::I64(v), p2));
    }
    if op == OP_F32_CONST {
        let (v, p1) = read_f32_bits(data, p)?;
        expect_const_type(ValueType::F32, expected)?;
        let p2 = read_expr_end(data, p1)?;
        return Ok((ConstExpr::F32(v), p2));
    }
    if op == OP_F64_CONST {
        let (v, p1) = read_f64_bits(data, p)?;
        expect_const_type(ValueType::F64, expected)?;
        let p2 = read_expr_end(data, p1)?;
        return Ok((ConstExpr::F64(v), p2));
    }
    if op == OP_GLOBAL_GET {
        let (idx, p1) = read_u32_leb(data, p)?;
        let gt = const_global(env, idx)?;
        expect_const_type(gt.valtype, expected)?;
        let p2 = read_expr_end(data, p1)?;
        return Ok((ConstExpr::GlobalGet(idx), p2));
    }
    Err(Error::InvalidConstExpr)
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

/// The type section entry at `idx`, copied out.
fn lookup_type(env: &Env, idx: u32) -> Result<FuncType> {
    let i = idx as usize;
    if i >= env.types.len() {
        return Err(Error::UnknownType(idx));
    }
    Ok(copy_func_type(&env.types[i]))
}

// --- The environment's sections ---

fn decode_type_section(data: &[u8], pos: usize, env: &mut Env) -> Result<usize> {
    let (count, p) = read_u32_leb(data, pos)?;
    let mut q = p;
    let mut i: u32 = 0;
    loop {
        if i >= count {
            return Ok(q);
        }
        let (ft, q1) = decode_func_type(data, q)?;
        env.types.push(ft);
        q = q1;
        i += 1;
    }
}

/// One import, pushed onto both the import list and its index space.
fn decode_import(data: &[u8], pos: usize, env: &mut Env) -> Result<usize> {
    let (module, p1) = decode_name(data, pos)?;
    let (name, p2) = decode_name(data, p1)?;
    let (kind, p3) = read_byte(data, p2)?;
    if kind == 0x00 {
        let (idx, p4) = read_u32_leb(data, p3)?;
        let ft = lookup_type(env, idx)?;
        env.func_types.push(ft);
        env.num_imported_funcs += 1;
        env.imports.push(Import {
            module,
            name,
            desc: ImportDesc::Func(idx),
        });
        return Ok(p4);
    }
    if kind == 0x01 {
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
        return Ok(p4);
    }
    if kind == 0x02 {
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
        return Ok(p4);
    }
    if kind == 0x03 {
        let (gt, p4) = decode_global_type(data, p3)?;
        env.global_types.push(gt);
        env.num_imported_globals += 1;
        env.imports.push(Import {
            module,
            name,
            desc: ImportDesc::Global(gt),
        });
        return Ok(p4);
    }
    Err(Error::InvalidType(kind))
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

/// Spec 3.4.11: export names are unique. Checked as each one is decoded, so
/// there is no second pass over the export list.
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
    if kind == 0x00 {
        if i >= env.func_types.len() {
            return Err(Error::UnknownFunc(idx));
        }
        return Ok(ExportDesc::Func(idx));
    }
    if kind == 0x01 {
        if i >= env.table_types.len() {
            return Err(Error::UnknownTable(idx));
        }
        return Ok(ExportDesc::Table(idx));
    }
    if kind == 0x02 {
        if i >= env.mem_types.len() {
            return Err(Error::UnknownMemory(idx));
        }
        return Ok(ExportDesc::Memory(idx));
    }
    if kind == 0x03 {
        if i >= env.global_types.len() {
            return Err(Error::UnknownGlobal(idx));
        }
        return Ok(ExportDesc::Global(idx));
    }
    Err(Error::InvalidType(kind))
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

/// Spec 3.4.13: the start function takes nothing and returns nothing.
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

fn decode_func_indices(data: &[u8], pos: usize, env: &Env) -> Result<(Vec<u32>, usize)> {
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

fn decode_element_section(data: &[u8], pos: usize, env: &mut Env) -> Result<usize> {
    let (count, p) = read_u32_leb(data, pos)?;
    let mut q = p;
    let mut i: u32 = 0;
    loop {
        if i >= count {
            return Ok(q);
        }
        let (table_idx, q1) = read_u32_leb(data, q)?;
        if table_idx as usize >= env.table_types.len() {
            return Err(Error::UnknownTable(table_idx));
        }
        let (offset, q2) = decode_const_expr(data, q1, env, ValueType::I32)?;
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

fn decode_env_section(data: &[u8], pos: usize, id: u8, env: &mut Env) -> Result<usize> {
    if id == SECTION_TYPE {
        return decode_type_section(data, pos, env);
    }
    if id == SECTION_IMPORT {
        return decode_import_section(data, pos, env);
    }
    if id == SECTION_FUNCTION {
        return decode_function_section(data, pos, env);
    }
    if id == SECTION_TABLE {
        return decode_table_section(data, pos, env);
    }
    if id == SECTION_MEMORY {
        return decode_memory_section(data, pos, env);
    }
    if id == SECTION_GLOBAL {
        return decode_global_section(data, pos, env);
    }
    if id == SECTION_EXPORT {
        return decode_export_section(data, pos, env);
    }
    if id == SECTION_START {
        return decode_start_section(data, pos, env);
    }
    if id == SECTION_ELEMENT {
        return decode_element_section(data, pos, env);
    }
    Err(Error::UnknownSection(id))
}

/// `decode_env_with` at the do-nothing consumer.
///
/// `decode_env_ok`, `decode_env_sound` and `decode_env_complete`, all under
/// the same size condition as `decode_env_with`.
pub fn decode_env(data: &[u8]) -> Result<(Env, usize)> {
    let mut nop = NopModuleVisitor;
    decode_env_with(data, &mut nop)
}

/// Decode and validate everything before the code section, reporting each
/// custom section it passes to `v`.
///
/// Returns the environment and the position of the next section's header,
/// which is where `validate_code` picks up. Both go on to the rest of the
/// walk: nothing else produces an `Env` the code section's entry points can be
/// trusted against.
///
/// **Precondition.** `data.len()` must be at most [`MAX_MODULE_BYTES`]. This
/// is where a decomposed caller owes it; `validate_module` and
/// `validate_module_with` check it themselves. Without it `decode_env_with_ok`
/// does not apply and nothing says this returns at all.
///
/// `decode_env_with_ok` (given `module_hooks_total`),
/// `Module_Sound.decode_env_driven` and `Module_Driven.decode_env_with_accepts`
/// (given `module_hooks_accept`), which carry `decode_env_sound` and
/// `decode_env_complete` across to a hooked run.
pub fn decode_env_with<V: ModuleVisitor>(data: &[u8], v: &mut V) -> Result<(Env, usize)> {
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
            let p = decode_env_section(data, start, id, &mut env)?;
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

/// Spec 5.5.13's `locals`: run-length encoded, flattened here.
fn decode_locals(data: &[u8], pos: usize) -> Result<(Vec<ValueType>, usize)> {
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

fn build_func_locals(params: &[ValueType], declared: &[ValueType]) -> Vec<ValueType> {
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

/// Validate one code-section entry, reporting each accepted operator to `v`.
///
/// `pos` is at the entry's size prefix and `index` selects its signature from
/// `env.func_type_indices`; the position just past the entry comes back. A
/// consumer that wants to compile or validate entries on separate threads
/// drives this rather than `validate_code`. It is a pure function of its four
/// value arguments, so nothing here says when or on which thread it runs.
///
/// **Preconditions.** All three are the caller's, and driving the section
/// through [`validate_code_with`] establishes all three:
///
/// - `env` came out of [`decode_env`] on this same `data`. Soundness is
///   stated relative to the environment handed over, so a fabricated one earns
///   a true theorem about no module; and `env_small`, which
///   `validate_code_entry_with_ok` needs, is `decode_env`'s postcondition and
///   nothing else's.
/// - `pos` is an entry start the code section's own framing gives: either
///   `CodeSection::entries` for the first, or the position a previous call
///   returned, or the `entry_pos` [`CodeVisitor::on_code_entry`] was handed.
///   `Module_Sound.code_entry_extent_frames` is what makes the last of those
///   the same position, and without it soundness says only that the operators
///   shown are the body of an entry at whatever offset was supplied.
/// - `pos <= data.len()` and `data.len() <= MAX_MODULE_BYTES`.
///
/// `Module_NoPanic.validate_code_entry_with_ok` (given `hooks_total`),
/// `Module_Sound.validate_code_entry_with_sound` -- which carries the trace, so
/// the operators `v` was shown are the body of the code entry those bytes
/// encode -- and `Module_Complete.validate_code_entry_with_complete` (given
/// `hooks_accept`).
///
/// A consumer that runs this from inside `on_code_entry` discharges its own
/// obligations with `Module_Driven.validate_code_entry_driven` for
/// `code_hooks_validate` and `Module_Driven.validate_code_entry_accepts` for
/// `code_hooks_accept`.
pub fn validate_code_entry_with<V: OpVisitor>(
    data: &[u8],
    pos: usize,
    env: &Env,
    index: usize,
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
    match opiter::validate_body_with(&data[p1..end], env, &ctx, v) {
        Ok(()) => Ok(end),
        Err(e) => Err(Error::Body(e)),
    }
}

/// Validate one code-section entry and nothing else.
///
/// `validate_code_entry_with` at the do-nothing consumer, with the same three
/// preconditions and the same three results without the hook hypotheses.
pub fn validate_code_entry(
    data: &[u8],
    pos: usize,
    env: &Env,
    index: usize,
) -> Result<usize> {
    let mut nop = NopVisitor;
    validate_code_entry_with(data, pos, env, index, &mut nop)
}

/// Frame each entry in turn and hand it to `v`, which validates it or takes on
/// the obligation to. The cursor moves by the extent the entry's own size
/// prefix gives, so where entry `k` starts does not wait on the `k` before it.
fn validate_code_entries_with<V: CodeVisitor>(
    data: &[u8],
    pos: usize,
    env: &Env,
    v: &mut V,
) -> Result<usize> {
    let mut q = pos;
    let mut i: usize = 0;
    loop {
        if i >= env.func_type_indices.len() {
            return Ok(q);
        }
        // Reading the size prefix costs at most MAX_LEB_BYTES, and framing the
        // entry says how far the whole of it reaches.
        v.on_need_bytes(q + MAX_LEB_BYTES)?;
        let (contents, end) = code_entry_extent(data, q)?;
        v.on_need_bytes(end)?;
        v.on_code_entry(data, env, i, q, contents, end)?;
        q = end;
        i += 1;
    }
}

/// The code section's header, once read: how many entries it declares, where
/// the first one starts, and where the section ends.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub struct CodeSection {
    /// Checked against the function section, so this is also the number of
    /// functions the module defines.
    pub count: u32,
    /// The first entry's size prefix, which is the `pos` that
    /// `validate_code_entry` takes.
    pub entries: usize,
    /// One past the section's last byte.
    pub end: usize,
}

/// Read the code section's header, if there is one.
///
/// `None` is a module with no code section, which is only allowed because it
/// declared no functions; a module that declared some and has no code section
/// is rejected here.
///
/// A consumer that drives `validate_code_entry` per function needs this to know
/// where the first one is, and cannot work it out without decoding the header
/// itself. `validate_code` is this, then the entries, then the framing check, so
/// the header has one reader rather than two.
///
/// **Precondition.** `pos` is [`decode_env`]'s returned position and `env` its
/// returned environment, both on this same `data`; `pos <= data.len()`.
///
/// `Module_NoPanic.code_section_ok`, `Module_Sound.code_section_sound` and
/// `Module_Complete.code_section_complete`. Reading the header is not
/// validating the section: a consumer that frames the entries itself from
/// `entries` owes the tiling check `validate_code_with` does at the end, and
/// `Module_Sound.validate_code_with_sound` is stated about the walk that does
/// it.
pub fn code_section(data: &[u8], pos: usize, env: &Env) -> Result<Option<CodeSection>> {
    if pos >= data.len() {
        return no_code_section(env);
    }
    let (id, start, end) = read_section_header(data, pos)?;
    if id != SECTION_CODE {
        return no_code_section(env);
    }
    let (count, p) = read_u32_leb(data, start)?;
    if count as usize != env.func_type_indices.len() {
        return Err(Error::FuncCodeMismatch);
    }
    Ok(Some(CodeSection {
        count,
        entries: p,
        end,
    }))
}

/// The function section fixed how many entries there have to be, so a missing
/// code section is an error exactly when the module declared functions.
fn no_code_section(env: &Env) -> Result<Option<CodeSection>> {
    if env.func_type_indices.is_empty() {
        return Ok(None);
    }
    Err(Error::MissingCodeSection)
}

/// Validate the code section, if there is one, reporting each entry to `v`.
///
/// The tiling check at the end is what pins the walk: each extent came from
/// that entry's own size prefix, and a chain of them that lands exactly on the
/// section's end is the partition the section's contents describe. A consumer
/// that framed the entries itself would owe this check; here it is inside.
///
/// **Preconditions.** `pos` and `env` are [`decode_env`]'s two return values
/// on this same `data`, and `data.len()` is at most [`MAX_MODULE_BYTES`]. What
/// `v` is trusted for is on [`CodeVisitor`], and there is more of it here than
/// anywhere else in this interface: taking `on_code_entry` means taking on that
/// entry's validation.
///
/// `Module_NoPanic.validate_code_with_ok` (given `code_hooks_total`),
/// `Module_Sound.validate_code_with_sound` and
/// `Module_Sound.validate_code_driven` (given `code_hooks_validate`), and
/// `Module_Complete.validate_code_with_complete` (given `code_hooks_accept`).
pub fn validate_code_with<V: CodeVisitor>(
    data: &[u8],
    pos: usize,
    env: &Env,
    v: &mut V,
) -> Result<usize> {
    // The section's header is its id, its size and the entry count.
    v.on_need_bytes(pos + MAX_CODE_HEADER_BYTES)?;
    let header = code_section(data, pos, env)?;
    match header {
        None => Ok(pos),
        Some(cs) => {
            let q = validate_code_entries_with(data, cs.entries, env, v)?;
            if q != cs.end {
                return Err(Error::SectionSizeMismatch);
            }
            Ok(cs.end)
        }
    }
}

/// `validate_code_with` at the consumer that validates each entry itself.
///
/// Same two preconditions as `validate_code_with`, and `validate_code_ok`,
/// `validate_code_sound` and `validate_code_complete` with no hook hypotheses.
pub fn validate_code(data: &[u8], pos: usize, env: &Env) -> Result<usize> {
    let mut v = ValidatingCodeVisitor;
    validate_code_with(data, pos, env, &mut v)
}

// --- The tail ---

fn decode_data_segment(data: &[u8], pos: usize, env: &Env) -> Result<(Data, usize)> {
    let (memory_idx, p1) = read_u32_leb(data, pos)?;
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

fn decode_data_section(data: &[u8], pos: usize, env: &Env) -> Result<(Vec<Data>, usize)> {
    let (count, p) = read_u32_leb(data, pos)?;
    let mut out = Vec::new();
    let mut q = p;
    let mut i: u32 = 0;
    loop {
        if i >= count {
            return Ok((out, q));
        }
        let (segment, q1) = decode_data_segment(data, q, env)?;
        out.push(segment);
        q = q1;
        i += 1;
    }
}

/// `decode_tail_with` at the do-nothing consumer.
///
/// `decode_tail_ok`, `decode_tail_sound` and `decode_tail_complete`, under the
/// same conditions as `decode_tail_with`.
pub fn decode_tail(data: &[u8], pos: usize, env: &Env) -> Result<Tail> {
    let mut nop = NopModuleVisitor;
    decode_tail_with(data, pos, env, &mut nop)
}

/// Decode and validate everything after the code section: the data section,
/// and any custom sections.
///
/// **Preconditions.** `pos` is what [`validate_code`] or
/// [`validate_code_with`] returned, `env` is [`decode_env`]'s, both on this
/// same `data`, and `data.len()` is at most [`MAX_MODULE_BYTES`].
///
/// `decode_tail_with_ok` (given `module_hooks_total`),
/// `Module_Sound.decode_tail_driven` and
/// `Module_Driven.decode_tail_with_accepts` (given `module_hooks_accept`).
pub fn decode_tail_with<V: ModuleVisitor>(
    data: &[u8],
    pos: usize,
    env: &Env,
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
            let (decoded, p) = decode_data_section(data, start, env)?;
            if p != end {
                return Err(Error::SectionSizeMismatch);
            }
            segments = decoded;
            q = end;
        }
    }
}

/// The extent of one code-section entry, without validating it: `pos` is at the
/// entry's size prefix, and the first byte of its contents and the position
/// just past it come back.
///
/// This reads the size prefix and nothing else, and decides nothing about
/// validity. It is how `validate_code_entries_with` frames an entry before
/// handing it over, which is what lets a consumer be told where entry `k` is
/// without the `k` before it having been validated. Private: an extent is only
/// sound to act on as part of a walk that goes on to show the extents tile the
/// section, and the walk is what does that.
fn code_entry_extent(data: &[u8], pos: usize) -> Result<(usize, usize)> {
    let (size, p) = read_u32_leb(data, pos)?;
    let n = size as usize;
    have_bytes(data, p, n)?;
    Ok((p, p + n))
}


/// What a consumer is told as a module is decoded around its code section.
///
/// One hook so far, and one trait for both ends of the module rather than one
/// each: a custom section is legal between any two others and the code section
/// cannot hold one, so the same consumer hears about the ones before the code
/// section from `decode_env_with` and the ones after it from
/// `decode_tail_with`, in module order, without caring which side reported
/// them.
///
/// Reported rather than carried on `Env` and `Tail`. A custom section is not
/// part of the module a binary denotes -- `Spec_Module.v` reads the format's
/// customs as padding -- and `chain_from` pins a decoded `Env` field for
/// field, so a field the walk grows and no theorem mentions would have to be
/// erased again before the chain could say anything. A hook keeps the decoded
/// record describing only what the theorems talk about.
///
/// Every hook has a default that does nothing, so a consumer fills in what it
/// wants and the rest costs nothing.
///
/// # What an implementation owes
///
/// Two obligations, both about code this crate does not contain, and both
/// written down in Coq:
///
/// - `Module_NoPanic.module_hooks_total`: every hook returns. It may not
///   panic and it may not loop. Without it nothing says `decode_env_with` or
///   `decode_tail_with` terminate.
/// - `Module_Complete.module_hooks_accept`: every hook returns `Ok`. Without
///   it a valid module may be rejected -- which is the interface working, and
///   is reported as `Error::Visitor` rather than as a verdict.
///
/// Neither can turn a rejection into an acceptance. Reporting a custom section
/// cannot change what is read next, so a `ModuleVisitor` has no obligation
/// beyond these two; `CodeVisitor` does.
pub trait ModuleVisitor {
    /// One custom section, framed and its name checked, but not otherwise
    /// read. Positions are into the bytes the decoder was handed.
    ///
    /// A report and not part of the verdict: a custom section is not part of
    /// the module a binary denotes, so nothing says the ranges reported are
    /// the custom sections the format says are there.
    fn on_custom_section(&mut self, _section: CustomSection) -> VisitResult {
        Ok(())
    }
}

/// The consumer that hears nothing, which is what `decode_env` and
/// `decode_tail` are: the `_with` entry points at a visitor that does nothing
/// with what it is shown.
pub struct NopModuleVisitor;
impl ModuleVisitor for NopModuleVisitor {}

/// What a consumer is told as the code section is walked.
///
/// Separate from `ModuleVisitor`, and its hooks return `Result<(), Error>`
/// rather than `VisitResult`, because its defaults are not the same kind of
/// thing. A `ModuleVisitor` hook reports something and does nothing by default;
/// `on_code_entry`'s default *is* the work, so the error it has to be able to
/// return is the validator's own.
///
/// The walk frames each entry and hands it over without validating it, which is
/// what a compiler that dispatches entries to other threads needs: entry `k`'s
/// position has to be known before the `k` before it have been validated.
///
/// # What an implementation owes
///
/// The two a `ModuleVisitor` owes, and a third that is the whole point of the
/// trait:
///
/// - `Module_NoPanic.code_hooks_total`: both hooks return.
/// - `Module_Complete.code_hooks_accept`: both return `Ok`, `on_code_entry`
///   at least for an entry `validate_code_entry` accepts.
/// - `Module_Sound.code_hooks_validate`: **`on_code_entry` returning `Ok`
///   means `validate_code_entry(data, entry_pos, env, index)` returns `Ok`.**
///   The walk does not validate the entry it hands over, so overriding this
///   hook is taking on that entry's validation. `validate_code_entry` is a
///   pure function of those four arguments, so the obligation says nothing
///   about when or on which thread the work happened.
///
/// A consumer that discharges the third by running
/// [`validate_code_entry_with`] at its own [`OpVisitor`] gets there with
/// `Module_Driven.validate_code_entry_driven`, and the second with
/// `Module_Driven.validate_code_entry_accepts`.
///
/// [`ValidatingCodeVisitor`] discharges all three
/// (`Module_Sound.validating_code_hooks_validate` and its two siblings), which
/// is why [`validate_code`] carries no hypotheses.
pub trait CodeVisitor {
    /// Before the walk reads the bytes up to `end`, exclusive. `end` may be
    /// past the input, which means "all of it": a consumer streaming the
    /// section blocks here until the bytes have arrived, and declines if they
    /// never will.
    ///
    /// Blocking is allowed; not returning is not. This is the hook where
    /// `code_hooks_total` is a real condition rather than a formality.
    fn on_need_bytes(&mut self, _end: usize) -> Result<()> {
        Ok(())
    }

    /// One entry, framed but not validated. `entry_pos` is at its size prefix,
    /// which is what `validate_code_entry` takes; `contents_start` is the first
    /// byte of the locals declarations, which is not where the body's code
    /// begins -- `on_function_start` reports that, after the declarations.
    ///
    /// Overriding this takes on the entry's validation: see
    /// `code_hooks_validate` above. `entry_pos` is a position the section's own
    /// framing gives, which `Module_Sound.code_entry_extent_frames` is what
    /// makes true, so it is the `pos` `validate_code_entry` wants.
    ///
    /// The default validates it in place, which is what a consumer that only
    /// wants a verdict wants.
    fn on_code_entry(
        &mut self,
        data: &[u8],
        env: &Env,
        index: usize,
        entry_pos: usize,
        _contents_start: usize,
        _entry_end: usize,
    ) -> Result<()> {
        let _ = validate_code_entry(data, entry_pos, env, index)?;
        Ok(())
    }
}

/// The consumer that takes every default: it waits for nothing and validates
/// each entry where it stands. `validate_code` is the walk at this one, which
/// is why that entry point owes nothing: `validating_code_hooks_total`,
/// `validating_code_hooks_accept` and `validating_code_hooks_validate` are
/// proved for this instance.
pub struct ValidatingCodeVisitor;
impl CodeVisitor for ValidatingCodeVisitor {}
