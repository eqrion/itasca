use itasca::error::*;
use itasca::types::*;

// ---- Module builder helper ----

/// Builds a Wasm module from sections, handling size encoding automatically.
struct ModuleBuilder {
    bytes: Vec<u8>,
}

impl ModuleBuilder {
    fn new() -> Self {
        let mut bytes = Vec::new();
        bytes.extend_from_slice(&[0x00, 0x61, 0x73, 0x6D]); // magic
        bytes.extend_from_slice(&[0x01, 0x00, 0x00, 0x00]); // version
        ModuleBuilder { bytes }
    }

    fn section(&mut self, id: u8, contents: &[u8]) -> &mut Self {
        self.bytes.push(id);
        self.push_leb128(contents.len() as u32);
        self.bytes.extend_from_slice(contents);
        self
    }

    fn push_leb128(&mut self, mut val: u32) {
        loop {
            let mut byte = (val & 0x7F) as u8;
            val >>= 7;
            if val != 0 {
                byte |= 0x80;
            }
            self.bytes.push(byte);
            if val == 0 {
                break;
            }
        }
    }

    fn build(self) -> Vec<u8> {
        self.bytes
    }
}

/// Encode a u32 as LEB128 bytes.
fn leb128_u32(mut val: u32) -> Vec<u8> {
    let mut out = Vec::new();
    loop {
        let mut byte = (val & 0x7F) as u8;
        val >>= 7;
        if val != 0 {
            byte |= 0x80;
        }
        out.push(byte);
        if val == 0 {
            break;
        }
    }
    out
}

/// Build a type section from function type descriptors.
/// Each entry: (params, results) as slices of value type bytes.
fn type_section(types: &[(&[u8], &[u8])]) -> Vec<u8> {
    let mut contents = Vec::new();
    contents.extend_from_slice(&leb128_u32(types.len() as u32));
    for (params, results) in types {
        contents.push(0x60);
        contents.extend_from_slice(&leb128_u32(params.len() as u32));
        contents.extend_from_slice(params);
        contents.extend_from_slice(&leb128_u32(results.len() as u32));
        contents.extend_from_slice(results);
    }
    contents
}

/// Build a function section from type indices.
fn func_section(indices: &[u32]) -> Vec<u8> {
    let mut contents = Vec::new();
    contents.extend_from_slice(&leb128_u32(indices.len() as u32));
    for idx in indices {
        contents.extend_from_slice(&leb128_u32(*idx));
    }
    contents
}

/// Build a code section from code entries: (locals, body_bytes).
/// Each local decl is (count, valtype_byte).
fn code_section(entries: &[(&[(u32, u8)], &[u8])]) -> Vec<u8> {
    let mut contents = Vec::new();
    contents.extend_from_slice(&leb128_u32(entries.len() as u32));
    for (locals, body) in entries {
        // Build the code entry body
        let mut entry = Vec::new();
        entry.extend_from_slice(&leb128_u32(locals.len() as u32));
        for (count, valtype) in *locals {
            entry.extend_from_slice(&leb128_u32(*count));
            entry.push(*valtype);
        }
        entry.extend_from_slice(body);
        entry.push(0x0B); // end
                          // Write entry size + entry
        contents.extend_from_slice(&leb128_u32(entry.len() as u32));
        contents.extend_from_slice(&entry);
    }
    contents
}

/// Build a memory section with one memory (min, optional max).
fn memory_section(min: u32, max: Option<u32>) -> Vec<u8> {
    let mut contents = Vec::new();
    contents.push(0x01); // count = 1
    match max {
        None => {
            contents.push(0x00);
            contents.extend_from_slice(&leb128_u32(min));
        }
        Some(m) => {
            contents.push(0x01);
            contents.extend_from_slice(&leb128_u32(min));
            contents.extend_from_slice(&leb128_u32(m));
        }
    }
    contents
}

/// Build a table section with one table (funcref, min, optional max).
fn table_section(min: u32, max: Option<u32>) -> Vec<u8> {
    let mut contents = Vec::new();
    contents.push(0x01); // count = 1
    contents.push(0x70); // funcref
    match max {
        None => {
            contents.push(0x00);
            contents.extend_from_slice(&leb128_u32(min));
        }
        Some(m) => {
            contents.push(0x01);
            contents.extend_from_slice(&leb128_u32(min));
            contents.extend_from_slice(&leb128_u32(m));
        }
    }
    contents
}

/// Build a global section from entries: (valtype, mutability, init_expr_bytes).
fn global_section(entries: &[(u8, u8, &[u8])]) -> Vec<u8> {
    let mut contents = Vec::new();
    contents.extend_from_slice(&leb128_u32(entries.len() as u32));
    for (valtype, mutability, init) in entries {
        contents.push(*valtype);
        contents.push(*mutability);
        contents.extend_from_slice(init);
        contents.push(0x0B); // end
    }
    contents
}

/// Build an export section from entries: (name, kind, index).
fn export_section(entries: &[(&str, u8, u32)]) -> Vec<u8> {
    let mut contents = Vec::new();
    contents.extend_from_slice(&leb128_u32(entries.len() as u32));
    for (name, kind, idx) in entries {
        contents.extend_from_slice(&leb128_u32(name.len() as u32));
        contents.extend_from_slice(name.as_bytes());
        contents.push(*kind);
        contents.extend_from_slice(&leb128_u32(*idx));
    }
    contents
}

/// Build an import section from entries: (module, name, desc_bytes).
fn import_section(entries: &[(&str, &str, &[u8])]) -> Vec<u8> {
    let mut contents = Vec::new();
    contents.extend_from_slice(&leb128_u32(entries.len() as u32));
    for (module, name, desc) in entries {
        contents.extend_from_slice(&leb128_u32(module.len() as u32));
        contents.extend_from_slice(module.as_bytes());
        contents.extend_from_slice(&leb128_u32(name.len() as u32));
        contents.extend_from_slice(name.as_bytes());
        contents.extend_from_slice(desc);
    }
    contents
}

/// Build a start section.
fn start_section(func_idx: u32) -> Vec<u8> {
    leb128_u32(func_idx)
}

/// Build an element section from entries: (table_idx, offset_expr_bytes, func_indices).
fn element_section(entries: &[(u32, &[u8], &[u32])]) -> Vec<u8> {
    let mut contents = Vec::new();
    contents.extend_from_slice(&leb128_u32(entries.len() as u32));
    for (table_idx, offset, funcs) in entries {
        contents.extend_from_slice(&leb128_u32(*table_idx));
        contents.extend_from_slice(offset);
        contents.push(0x0B); // end expr
        contents.extend_from_slice(&leb128_u32(funcs.len() as u32));
        for f in *funcs {
            contents.extend_from_slice(&leb128_u32(*f));
        }
    }
    contents
}

/// Build a data section from entries: (memory_idx, offset_expr_bytes, data).
fn data_section(entries: &[(u32, &[u8], &[u8])]) -> Vec<u8> {
    let mut contents = Vec::new();
    contents.extend_from_slice(&leb128_u32(entries.len() as u32));
    for (mem_idx, offset, data) in entries {
        contents.extend_from_slice(&leb128_u32(*mem_idx));
        contents.extend_from_slice(offset);
        contents.push(0x0B); // end expr
        contents.extend_from_slice(&leb128_u32(data.len() as u32));
        contents.extend_from_slice(data);
    }
    contents
}

/// Convenience: build a one-function module given type and body bytes.
fn one_func_module(params: &[u8], results: &[u8], locals: &[(u32, u8)], body: &[u8]) -> Vec<u8> {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(params, results)]));
    b.section(3, &func_section(&[0]));
    b.section(10, &code_section(&[(locals, body)]));
    b.build()
}

const I32: u8 = 0x7F;
const I64: u8 = 0x7E;
const F32: u8 = 0x7D;
const F64: u8 = 0x7C;

// ---- Helper: build a minimal valid wasm module ----

/// Minimal valid module: magic + version + no sections.
const MINIMAL_MODULE: &[u8] = &[
    0x00, 0x61, 0x73, 0x6D, // magic
    0x01, 0x00, 0x00, 0x00, // version 1
];

/// Module with a single type ([] -> []) and a single function (empty body).
fn module_with_empty_func() -> Vec<u8> {
    let mut bytes = Vec::new();
    // Header
    bytes.extend_from_slice(&[0x00, 0x61, 0x73, 0x6D]);
    bytes.extend_from_slice(&[0x01, 0x00, 0x00, 0x00]);

    // Type section (id=1): 1 type, [] -> []
    bytes.push(0x01); // section id
    bytes.push(0x04); // section size
    bytes.push(0x01); // count = 1
    bytes.push(0x60); // func type tag
    bytes.push(0x00); // 0 params
    bytes.push(0x00); // 0 results

    // Function section (id=3): 1 function, type index 0
    bytes.push(0x03); // section id
    bytes.push(0x02); // section size
    bytes.push(0x01); // count = 1
    bytes.push(0x00); // type index 0

    // Code section (id=10): 1 code entry, 0 locals, body = [end]
    bytes.push(0x0A); // section id
    bytes.push(0x04); // section size
    bytes.push(0x01); // count = 1
    bytes.push(0x02); // body size = 2
    bytes.push(0x00); // 0 local decls
    bytes.push(0x0B); // end

    bytes
}

/// Module with a function that takes i32 and returns i32 (identity).
fn module_with_i32_identity() -> Vec<u8> {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&[0x00, 0x61, 0x73, 0x6D]);
    bytes.extend_from_slice(&[0x01, 0x00, 0x00, 0x00]);

    // Type section: [i32] -> [i32]
    // contents: 01 60 01 7F 01 7F = 6 bytes
    bytes.push(0x01); // section id
    bytes.push(0x06); // section size
    bytes.push(0x01); // count
    bytes.push(0x60); // func
    bytes.push(0x01); // 1 param
    bytes.push(0x7F); // i32
    bytes.push(0x01); // 1 result
    bytes.push(0x7F); // i32

    // Function section: 01 00 = 2 bytes
    bytes.push(0x03);
    bytes.push(0x02);
    bytes.push(0x01);
    bytes.push(0x00);

    // Code section: body = [local.get 0, end]
    // body bytes: 00 20 00 0B = 4 bytes, so body size = 4
    // code entry: 04 00 20 00 0B = 5 bytes
    // section contents: 01 04 00 20 00 0B = 6 bytes
    bytes.push(0x0A);
    bytes.push(0x06); // section size
    bytes.push(0x01); // count
    bytes.push(0x04); // body size
    bytes.push(0x00); // 0 locals
    bytes.push(0x20); // local.get
    bytes.push(0x00); // index 0
    bytes.push(0x0B); // end

    bytes
}

// ---- Decode tests ----

#[test]
fn test_decode_minimal_module() {
    let m = itasca::validate_module(MINIMAL_MODULE).unwrap();
    assert!(m.env.types.is_empty());
    assert!(m.env.func_type_indices.is_empty());
    assert!(m.env.table_types.is_empty());
    assert!(m.env.mem_types.is_empty());
    assert!(m.env.globals.is_empty());
    assert!(m.env.exports.is_empty());
    assert!(m.env.imports.is_empty());
    assert!(m.env.start.is_none());
    assert!(m.tail.data.is_empty());
}

#[test]
fn test_decode_invalid_magic() {
    let bytes = [0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00];
    assert_eq!(itasca::validate_module(&bytes), Err(Error::InvalidMagic));
}

#[test]
fn test_decode_invalid_version() {
    let bytes = [0x00, 0x61, 0x73, 0x6D, 0x02, 0x00, 0x00, 0x00];
    assert_eq!(itasca::validate_module(&bytes), Err(Error::InvalidVersion));
}

#[test]
fn test_decode_truncated() {
    let bytes = [0x00, 0x61, 0x73];
    assert_eq!(
        itasca::validate_module(&bytes),
        Err(Error::Read(OpError::UnexpectedEof))
    );
}

#[test]
fn test_decode_empty_func() {
    let bytes = module_with_empty_func();
    let m = itasca::validate_module(&bytes).unwrap();
    assert_eq!(m.env.types.len(), 1);
    assert_eq!(m.env.func_type_indices, vec![0]);
    assert_eq!(m.env.func_types.len(), 1);
    assert_eq!(m.env.num_imported_funcs, 0);
}

#[test]
fn test_decode_i32_identity() {
    let bytes = module_with_i32_identity();
    let m = itasca::validate_module(&bytes).unwrap();
    assert_eq!(m.env.types[0].params, vec![ValueType::I32]);
    assert_eq!(m.env.types[0].results, vec![ValueType::I32]);
}

#[test]
fn test_decode_section_out_of_order() {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&[0x00, 0x61, 0x73, 0x6D]);
    bytes.extend_from_slice(&[0x01, 0x00, 0x00, 0x00]);

    // Function section (id=3) before type section (id=1) - invalid
    bytes.push(0x03); // function section
    bytes.push(0x01);
    bytes.push(0x00);

    bytes.push(0x01); // type section
    bytes.push(0x01);
    bytes.push(0x00);

    assert_eq!(
        itasca::validate_module(&bytes),
        Err(Error::SectionOutOfOrder)
    );
}

// ---- Validate tests ----

#[test]
fn test_validate_minimal_module() {
    itasca::validate_module(MINIMAL_MODULE).unwrap();
}

#[test]
fn test_validate_empty_func() {
    let bytes = module_with_empty_func();
    itasca::validate_module(&bytes).unwrap();
}

#[test]
fn test_validate_i32_identity() {
    let bytes = module_with_i32_identity();
    itasca::validate_module(&bytes).unwrap();
}

#[test]
fn test_validate_type_mismatch() {
    // Function declared as [] -> [i32] but body is empty (returns nothing)
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&[0x00, 0x61, 0x73, 0x6D]);
    bytes.extend_from_slice(&[0x01, 0x00, 0x00, 0x00]);

    // Type: [] -> [i32]
    bytes.push(0x01);
    bytes.push(0x05);
    bytes.push(0x01);
    bytes.push(0x60);
    bytes.push(0x00);
    bytes.push(0x01);
    bytes.push(0x7F);

    // Function section
    bytes.push(0x03);
    bytes.push(0x02);
    bytes.push(0x01);
    bytes.push(0x00);

    // Code: empty body
    bytes.push(0x0A);
    bytes.push(0x04);
    bytes.push(0x01);
    bytes.push(0x02);
    bytes.push(0x00);
    bytes.push(0x0B);

    assert!(itasca::validate_module(&bytes).is_err());
}

#[test]
fn test_validate_i32_add() {
    // Function [i32, i32] -> [i32], body = [local.get 0, local.get 1, i32.add]
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&[0x00, 0x61, 0x73, 0x6D]);
    bytes.extend_from_slice(&[0x01, 0x00, 0x00, 0x00]);

    // Type: [i32, i32] -> [i32]
    bytes.push(0x01);
    bytes.push(0x07);
    bytes.push(0x01);
    bytes.push(0x60);
    bytes.push(0x02);
    bytes.push(0x7F);
    bytes.push(0x7F);
    bytes.push(0x01);
    bytes.push(0x7F);

    // Function section
    bytes.push(0x03);
    bytes.push(0x02);
    bytes.push(0x01);
    bytes.push(0x00);

    // Code
    bytes.push(0x0A);
    bytes.push(0x09);
    bytes.push(0x01);
    bytes.push(0x07); // body size
    bytes.push(0x00); // 0 locals
    bytes.push(0x20); // local.get
    bytes.push(0x00); // 0
    bytes.push(0x20); // local.get
    bytes.push(0x01); // 1
    bytes.push(0x6A); // i32.add
    bytes.push(0x0B); // end

    itasca::validate_module(&bytes).unwrap();
}

#[test]
fn test_validate_block() {
    // Function [] -> [i32], body = [block (result i32) [i32.const 42] end]
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&[0x00, 0x61, 0x73, 0x6D]);
    bytes.extend_from_slice(&[0x01, 0x00, 0x00, 0x00]);

    // Type: [] -> [i32]
    bytes.push(0x01);
    bytes.push(0x05);
    bytes.push(0x01);
    bytes.push(0x60);
    bytes.push(0x00);
    bytes.push(0x01);
    bytes.push(0x7F);

    // Function section
    bytes.push(0x03);
    bytes.push(0x02);
    bytes.push(0x01);
    bytes.push(0x00);

    // Code: block (result i32) i32.const 42 end
    bytes.push(0x0A);
    bytes.push(0x09);
    bytes.push(0x01);
    bytes.push(0x07); // body size
    bytes.push(0x00); // 0 locals
    bytes.push(0x02); // block
    bytes.push(0x7F); // result i32
    bytes.push(0x41); // i32.const
    bytes.push(0x2A); // 42
    bytes.push(0x0B); // end (block)
    bytes.push(0x0B); // end (func)

    itasca::validate_module(&bytes).unwrap();
}

#[test]
fn test_validate_unreachable_polymorphism() {
    // Function [] -> [i32], body = [unreachable]
    // This is valid: unreachable produces any type
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&[0x00, 0x61, 0x73, 0x6D]);
    bytes.extend_from_slice(&[0x01, 0x00, 0x00, 0x00]);

    // Type: [] -> [i32]
    bytes.push(0x01);
    bytes.push(0x05);
    bytes.push(0x01);
    bytes.push(0x60);
    bytes.push(0x00);
    bytes.push(0x01);
    bytes.push(0x7F);

    // Function section
    bytes.push(0x03);
    bytes.push(0x02);
    bytes.push(0x01);
    bytes.push(0x00);

    // Code: unreachable
    bytes.push(0x0A);
    bytes.push(0x05);
    bytes.push(0x01);
    bytes.push(0x03); // body size
    bytes.push(0x00); // 0 locals
    bytes.push(0x00); // unreachable
    bytes.push(0x0B); // end

    itasca::validate_module(&bytes).unwrap();
}

#[test]
fn test_validate_if_else() {
    // Function [i32] -> [i32], body = [local.get 0, if (result i32) i32.const 1 else i32.const 0 end]
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&[0x00, 0x61, 0x73, 0x6D]);
    bytes.extend_from_slice(&[0x01, 0x00, 0x00, 0x00]);

    // Type: [i32] -> [i32]
    bytes.push(0x01);
    bytes.push(0x06);
    bytes.push(0x01);
    bytes.push(0x60);
    bytes.push(0x01);
    bytes.push(0x7F);
    bytes.push(0x01);
    bytes.push(0x7F);

    // Function section
    bytes.push(0x03);
    bytes.push(0x02);
    bytes.push(0x01);
    bytes.push(0x00);

    // Code
    bytes.push(0x0A);
    bytes.push(0x0E); // section size
    bytes.push(0x01); // count
    bytes.push(0x0C); // body size
    bytes.push(0x00); // 0 locals
    bytes.push(0x20); // local.get
    bytes.push(0x00); // 0
    bytes.push(0x04); // if
    bytes.push(0x7F); // result i32
    bytes.push(0x41); // i32.const
    bytes.push(0x01); // 1
    bytes.push(0x05); // else
    bytes.push(0x41); // i32.const
    bytes.push(0x00); // 0
    bytes.push(0x0B); // end (if)
    bytes.push(0x0B); // end (func)

    itasca::validate_module(&bytes).unwrap();
}

#[test]
fn test_validate_memory_operations() {
    // Function with memory: [i32] -> [i32], body = [local.get 0, i32.load]
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&[0x00, 0x61, 0x73, 0x6D]);
    bytes.extend_from_slice(&[0x01, 0x00, 0x00, 0x00]);

    // Type: [i32] -> [i32]
    bytes.push(0x01);
    bytes.push(0x06);
    bytes.push(0x01);
    bytes.push(0x60);
    bytes.push(0x01);
    bytes.push(0x7F);
    bytes.push(0x01);
    bytes.push(0x7F);

    // Function section
    bytes.push(0x03);
    bytes.push(0x02);
    bytes.push(0x01);
    bytes.push(0x00);

    // Memory section (id=5): 1 memory, min=1, no max
    bytes.push(0x05);
    bytes.push(0x03);
    bytes.push(0x01);
    bytes.push(0x00);
    bytes.push(0x01);

    // Code
    bytes.push(0x0A);
    bytes.push(0x09);
    bytes.push(0x01);
    bytes.push(0x07); // body size
    bytes.push(0x00); // 0 locals
    bytes.push(0x20); // local.get
    bytes.push(0x00); // 0
    bytes.push(0x28); // i32.load
    bytes.push(0x02); // align=2
    bytes.push(0x00); // offset=0
    bytes.push(0x0B); // end

    itasca::validate_module(&bytes).unwrap();
}

#[test]
fn test_validate_no_memory_for_load() {
    // Function with i32.load but no memory - should fail
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&[0x00, 0x61, 0x73, 0x6D]);
    bytes.extend_from_slice(&[0x01, 0x00, 0x00, 0x00]);

    // Type: [i32] -> [i32]
    bytes.push(0x01);
    bytes.push(0x06);
    bytes.push(0x01);
    bytes.push(0x60);
    bytes.push(0x01);
    bytes.push(0x7F);
    bytes.push(0x01);
    bytes.push(0x7F);

    // Function section
    bytes.push(0x03);
    bytes.push(0x02);
    bytes.push(0x01);
    bytes.push(0x00);

    // Code (no memory section!)
    bytes.push(0x0A);
    bytes.push(0x09);
    bytes.push(0x01);
    bytes.push(0x07);
    bytes.push(0x00);
    bytes.push(0x20);
    bytes.push(0x00);
    bytes.push(0x28);
    bytes.push(0x02);
    bytes.push(0x00);
    bytes.push(0x0B);

    assert!(itasca::validate_module(&bytes).is_err());
}

#[test]
fn test_validate_duplicate_export_name() {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&[0x00, 0x61, 0x73, 0x6D]);
    bytes.extend_from_slice(&[0x01, 0x00, 0x00, 0x00]);

    // Type section: [] -> []
    bytes.push(0x01);
    bytes.push(0x04);
    bytes.push(0x01);
    bytes.push(0x60);
    bytes.push(0x00);
    bytes.push(0x00);

    // Function section
    bytes.push(0x03);
    bytes.push(0x03);
    bytes.push(0x02); // 2 functions
    bytes.push(0x00);
    bytes.push(0x00);

    // Export section: two exports with same name "f"
    // Each export: 01 66 00 xx = 4 bytes, so 2 exports = 8 bytes + 1 count = 9
    bytes.push(0x07);
    bytes.push(0x09);
    bytes.push(0x02); // 2 exports
    bytes.push(0x01); // name len
    bytes.push(b'f'); // name
    bytes.push(0x00); // func
    bytes.push(0x00); // index 0
    bytes.push(0x01); // name len
    bytes.push(b'f'); // name (duplicate!)
    bytes.push(0x00); // func
    bytes.push(0x01); // index 1

    // Code section: 2 empty bodies
    bytes.push(0x0A);
    bytes.push(0x07);
    bytes.push(0x02);
    bytes.push(0x02);
    bytes.push(0x00);
    bytes.push(0x0B);
    bytes.push(0x02);
    bytes.push(0x00);
    bytes.push(0x0B);

    assert_eq!(
        itasca::validate_module(&bytes),
        Err(Error::DuplicateExportName)
    );
}

#[test]
fn test_validate_br_in_block() {
    // Function [] -> [i32], body = [block (result i32) i32.const 1 br 0 end]
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&[0x00, 0x61, 0x73, 0x6D]);
    bytes.extend_from_slice(&[0x01, 0x00, 0x00, 0x00]);

    // Type: [] -> [i32]
    bytes.push(0x01);
    bytes.push(0x05);
    bytes.push(0x01);
    bytes.push(0x60);
    bytes.push(0x00);
    bytes.push(0x01);
    bytes.push(0x7F);

    // Function section
    bytes.push(0x03);
    bytes.push(0x02);
    bytes.push(0x01);
    bytes.push(0x00);

    // Code
    bytes.push(0x0A);
    bytes.push(0x0B);
    bytes.push(0x01);
    bytes.push(0x09); // body size
    bytes.push(0x00);
    bytes.push(0x02); // block
    bytes.push(0x7F); // result i32
    bytes.push(0x41); // i32.const
    bytes.push(0x01); // 1
    bytes.push(0x0C); // br
    bytes.push(0x00); // label 0
    bytes.push(0x0B); // end block
    bytes.push(0x0B); // end func

    itasca::validate_module(&bytes).unwrap();
}

// ---- Decode + validate round-trip ----

#[test]
fn test_decode_and_validate_minimal() {
    itasca::validate_module(MINIMAL_MODULE).unwrap();
}

#[test]
fn test_decode_and_validate_with_locals() {
    // Function [] -> [i32] with one i32 local
    // Body: i32.const 5, local.set 0, local.get 0
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&[0x00, 0x61, 0x73, 0x6D]);
    bytes.extend_from_slice(&[0x01, 0x00, 0x00, 0x00]);

    // Type: [] -> [i32]
    bytes.push(0x01);
    bytes.push(0x05);
    bytes.push(0x01);
    bytes.push(0x60);
    bytes.push(0x00);
    bytes.push(0x01);
    bytes.push(0x7F);

    // Function section
    bytes.push(0x03);
    bytes.push(0x02);
    bytes.push(0x01);
    bytes.push(0x00);

    // Code
    bytes.push(0x0A);
    bytes.push(0x0C);
    bytes.push(0x01);
    bytes.push(0x0A); // body size
    bytes.push(0x01); // 1 local decl
    bytes.push(0x01); // count=1
    bytes.push(0x7F); // i32
    bytes.push(0x41); // i32.const
    bytes.push(0x05); // 5
    bytes.push(0x21); // local.set
    bytes.push(0x00); // index 0
    bytes.push(0x20); // local.get
    bytes.push(0x00); // index 0
    bytes.push(0x0B); // end

    itasca::validate_module(&bytes).unwrap();
}

#[test]
fn test_validate_loop() {
    // Function [] -> [], body = [loop (empty) nop end]
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&[0x00, 0x61, 0x73, 0x6D]);
    bytes.extend_from_slice(&[0x01, 0x00, 0x00, 0x00]);

    // Type: [] -> []
    bytes.push(0x01);
    bytes.push(0x04);
    bytes.push(0x01);
    bytes.push(0x60);
    bytes.push(0x00);
    bytes.push(0x00);

    // Function section
    bytes.push(0x03);
    bytes.push(0x02);
    bytes.push(0x01);
    bytes.push(0x00);

    // Code: loop (empty) nop end
    bytes.push(0x0A);
    bytes.push(0x08);
    bytes.push(0x01);
    bytes.push(0x06); // body size
    bytes.push(0x00);
    bytes.push(0x03); // loop
    bytes.push(0x40); // empty block type
    bytes.push(0x01); // nop
    bytes.push(0x0B); // end loop
    bytes.push(0x0B); // end func

    itasca::validate_module(&bytes).unwrap();
}

#[test]
fn test_validate_select() {
    // Function [i32, i32, i32] -> [i32], body = [local.get 0, local.get 1, local.get 2, select]
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&[0x00, 0x61, 0x73, 0x6D]);
    bytes.extend_from_slice(&[0x01, 0x00, 0x00, 0x00]);

    // Type: [i32, i32, i32] -> [i32]
    bytes.push(0x01);
    bytes.push(0x08);
    bytes.push(0x01);
    bytes.push(0x60);
    bytes.push(0x03); // 3 params
    bytes.push(0x7F);
    bytes.push(0x7F);
    bytes.push(0x7F);
    bytes.push(0x01); // 1 result
    bytes.push(0x7F);

    // Function section
    bytes.push(0x03);
    bytes.push(0x02);
    bytes.push(0x01);
    bytes.push(0x00);

    // Code
    bytes.push(0x0A);
    bytes.push(0x0B);
    bytes.push(0x01);
    bytes.push(0x09); // body size
    bytes.push(0x00);
    bytes.push(0x20);
    bytes.push(0x00); // local.get 0
    bytes.push(0x20);
    bytes.push(0x01); // local.get 1
    bytes.push(0x20);
    bytes.push(0x02); // local.get 2
    bytes.push(0x1B); // select
    bytes.push(0x0B);

    itasca::validate_module(&bytes).unwrap();
}

#[test]
fn test_validate_global_const_expr() {
    // Module with a global i32 initialized to i32.const 42
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&[0x00, 0x61, 0x73, 0x6D]);
    bytes.extend_from_slice(&[0x01, 0x00, 0x00, 0x00]);

    // Global section (id=6)
    bytes.push(0x06);
    bytes.push(0x06);
    bytes.push(0x01); // 1 global
    bytes.push(0x7F); // i32
    bytes.push(0x00); // const
    bytes.push(0x41); // i32.const
    bytes.push(0x2A); // 42
    bytes.push(0x0B); // end

    itasca::validate_module(&bytes).unwrap();
}

#[test]
fn test_validate_global_mutable_in_const_expr() {
    // Module with a global trying to use global.get of a non-imported global
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&[0x00, 0x61, 0x73, 0x6D]);
    bytes.extend_from_slice(&[0x01, 0x00, 0x00, 0x00]);

    // Global section: 2 globals, second uses global.get 0
    bytes.push(0x06);
    bytes.push(0x0B);
    bytes.push(0x02);
    // Global 0: i32 const = 1
    bytes.push(0x7F);
    bytes.push(0x00);
    bytes.push(0x41);
    bytes.push(0x01);
    bytes.push(0x0B);
    // Global 1: i32 const = global.get 0 (not imported - invalid!)
    bytes.push(0x7F);
    bytes.push(0x00);
    bytes.push(0x23);
    bytes.push(0x00);
    bytes.push(0x0B);

    assert!(itasca::validate_module(&bytes).is_err());
}

// ---- Edge case tests using builder helpers ----

#[test]
fn test_call_indirect() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[I32], &[I32])]));
    b.section(3, &func_section(&[0]));
    b.section(4, &table_section(1, None));
    b.section(
        10,
        &code_section(&[(
            &[],
            &[
                0x41, 0x00, // i32.const 0 (argument)
                0x41, 0x00, // i32.const 0 (table index)
                0x11, 0x00, 0x00, // call_indirect type=0, table=0
            ],
        )]),
    );
    itasca::validate_module(&b.build()).unwrap();
}

#[test]
fn test_call_indirect_no_table() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[I32], &[I32])]));
    b.section(3, &func_section(&[0]));
    b.section(
        10,
        &code_section(&[(&[], &[0x41, 0x00, 0x41, 0x00, 0x11, 0x00, 0x00])]),
    );
    assert!(itasca::validate_module(&b.build()).is_err());
}

#[test]
fn test_br_table() {
    let bytes = one_func_module(
        &[I32],
        &[I32],
        &[],
        &[
            0x02, 0x7F, // block (result i32)
            0x02, 0x7F, //   block (result i32)
            0x20, 0x00, //     local.get 0
            0x41, 0x01, //     i32.const 1
            0x0E, 0x02, //     br_table vec_len=2
            0x00, 0x01, //       labels [0, 1]
            0x00, //       default 0
            0x0B, //   end
            0x0B, // end
        ],
    );
    itasca::validate_module(&bytes).unwrap();
}

#[test]
fn test_br_table_arity_mismatch() {
    let bytes = one_func_module(
        &[I32],
        &[I32],
        &[],
        &[
            0x02, 0x7F, // block (result i32)
            0x02, 0x7E, //   block (result i64)
            0x20, 0x00, //     local.get 0 (i32)
            0x0E, 0x01, //     br_table vec_len=1
            0x01, //       labels [1] (i32 block)
            0x00, //       default 0 (i64 block) - mismatch!
            0x0B, //   end
            0x0B, // end
        ],
    );
    assert!(itasca::validate_module(&bytes).is_err());
}

#[test]
fn test_return_from_function() {
    let bytes = one_func_module(
        &[],
        &[I32],
        &[],
        &[
            0x41, 0x2A, 0x0F, // i32.const 42, return
        ],
    );
    itasca::validate_module(&bytes).unwrap();
}

#[test]
fn test_return_wrong_type() {
    let bytes = one_func_module(
        &[],
        &[I32],
        &[],
        &[
            0x42, 0x2A, 0x0F, // i64.const 42, return -- wrong type
        ],
    );
    assert!(itasca::validate_module(&bytes).is_err());
}

#[test]
fn test_drop_after_unreachable() {
    let bytes = one_func_module(&[], &[], &[], &[0x00, 0x1A]); // unreachable, drop
    itasca::validate_module(&bytes).unwrap();
}

#[test]
fn test_select_after_unreachable() {
    let bytes = one_func_module(&[], &[I32], &[], &[0x00, 0x1B]); // unreachable, select
    itasca::validate_module(&bytes).unwrap();
}

#[test]
fn test_nested_blocks_deep() {
    let bytes = one_func_module(
        &[],
        &[I32],
        &[],
        &[
            0x02, 0x7F, // block (result i32)
            0x02, 0x7F, //   block (result i32)
            0x02, 0x7F, //     block (result i32)
            0x41, 0x01, //       i32.const 1
            0x0C, 0x02, //       br 2 (outermost)
            0x0B, 0x0B, 0x0B,
        ],
    );
    itasca::validate_module(&bytes).unwrap();
}

#[test]
fn test_br_unknown_label() {
    let bytes = one_func_module(
        &[],
        &[],
        &[],
        &[
            0x02, 0x40, 0x0C, 0x05, 0x0B, // block, br 5, end
        ],
    );
    assert!(itasca::validate_module(&bytes).is_err());
}

#[test]
fn test_local_tee() {
    let bytes = one_func_module(
        &[I32],
        &[I32],
        &[],
        &[
            0x20, 0x00, 0x22, 0x00, // local.get 0, local.tee 0
        ],
    );
    itasca::validate_module(&bytes).unwrap();
}

#[test]
fn test_unknown_local() {
    let bytes = one_func_module(&[], &[I32], &[], &[0x20, 0x63]); // local.get 99
    assert_eq!(
        itasca::validate_module(&bytes),
        Err(Error::Body(OpError::UnknownLocal))
    );
}

#[test]
fn test_global_set_immutable() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[], &[])]));
    b.section(3, &func_section(&[0]));
    b.section(6, &global_section(&[(I32, 0x00, &[0x41, 0x00])]));
    b.section(10, &code_section(&[(&[], &[0x41, 0x01, 0x24, 0x00])]));
    assert!(itasca::validate_module(&b.build()).is_err());
}

#[test]
fn test_global_set_mutable() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[], &[])]));
    b.section(3, &func_section(&[0]));
    b.section(6, &global_section(&[(I32, 0x01, &[0x41, 0x00])]));
    b.section(10, &code_section(&[(&[], &[0x41, 0x01, 0x24, 0x00])]));
    itasca::validate_module(&b.build()).unwrap();
}

#[test]
fn test_memory_store() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[I32, I32], &[])]));
    b.section(3, &func_section(&[0]));
    b.section(5, &memory_section(1, None));
    b.section(
        10,
        &code_section(&[(&[], &[0x20, 0x00, 0x20, 0x01, 0x36, 0x02, 0x00])]),
    );
    itasca::validate_module(&b.build()).unwrap();
}

#[test]
fn test_memory_invalid_alignment() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[I32], &[I32])]));
    b.section(3, &func_section(&[0]));
    b.section(5, &memory_section(1, None));
    b.section(10, &code_section(&[(&[], &[0x20, 0x00, 0x28, 0x03, 0x00])]));
    assert_eq!(
        itasca::validate_module(&b.build()),
        Err(Error::Body(OpError::InvalidAlignment))
    );
}

#[test]
fn test_memory_size_grow() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[], &[I32])]));
    b.section(3, &func_section(&[0]));
    b.section(5, &memory_section(1, None));
    b.section(10, &code_section(&[(&[], &[0x3F, 0x00, 0x40, 0x00])]));
    itasca::validate_module(&b.build()).unwrap();
}

#[test]
fn test_multiple_locals() {
    let bytes = one_func_module(&[], &[I64], &[(3, I32), (2, I64)], &[0x20, 0x04]);
    itasca::validate_module(&bytes).unwrap();
}

#[test]
fn test_call_between_functions() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[], &[I32])]));
    b.section(3, &func_section(&[0, 0]));
    b.section(
        10,
        &code_section(&[
            (&[], &[0x10, 0x01]), // call func 1
            (&[], &[0x41, 0x2A]), // i32.const 42
        ]),
    );
    itasca::validate_module(&b.build()).unwrap();
}

#[test]
fn test_call_unknown_function() {
    let bytes = one_func_module(&[], &[], &[], &[0x10, 0x05]);
    assert!(itasca::validate_module(&bytes).is_err());
}

#[test]
fn test_start_function_valid() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[], &[])]));
    b.section(3, &func_section(&[0]));
    b.section(8, &start_section(0));
    b.section(10, &code_section(&[(&[], &[])]));
    itasca::validate_module(&b.build()).unwrap();
}

#[test]
fn test_start_function_wrong_type() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[I32], &[])]));
    b.section(3, &func_section(&[0]));
    b.section(8, &start_section(0));
    b.section(10, &code_section(&[(&[], &[])]));
    assert_eq!(
        itasca::validate_module(&b.build()),
        Err(Error::InvalidStartType)
    );
}

#[test]
fn test_start_function_unknown() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[], &[])]));
    b.section(3, &func_section(&[0]));
    b.section(8, &start_section(99));
    b.section(10, &code_section(&[(&[], &[])]));
    assert!(itasca::validate_module(&b.build()).is_err());
}

#[test]
fn test_export_function() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[], &[])]));
    b.section(3, &func_section(&[0]));
    b.section(7, &export_section(&[("main", 0x00, 0)]));
    b.section(10, &code_section(&[(&[], &[])]));
    itasca::validate_module(&b.build()).unwrap();
}

#[test]
fn test_export_memory() {
    let mut b = ModuleBuilder::new();
    b.section(5, &memory_section(1, None));
    b.section(7, &export_section(&[("memory", 0x02, 0)]));
    itasca::validate_module(&b.build()).unwrap();
}

#[test]
fn test_export_unknown_func_index() {
    let mut b = ModuleBuilder::new();
    b.section(7, &export_section(&[("f", 0x00, 5)]));
    assert!(itasca::validate_module(&b.build()).is_err());
}

#[test]
fn test_import_function() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[], &[I32])]));
    b.section(2, &import_section(&[("env", "foo", &[0x00, 0x00])]));
    b.section(3, &func_section(&[0]));
    b.section(10, &code_section(&[(&[], &[0x10, 0x00])])); // call imported func
    itasca::validate_module(&b.build()).unwrap();
}

#[test]
fn test_import_global_in_const_expr() {
    let mut b = ModuleBuilder::new();
    b.section(2, &import_section(&[("env", "g", &[0x03, I32, 0x00])]));
    b.section(6, &global_section(&[(I32, 0x00, &[0x23, 0x00])]));
    itasca::validate_module(&b.build()).unwrap();
}

#[test]
fn test_import_mutable_global_in_const_expr() {
    let mut b = ModuleBuilder::new();
    b.section(2, &import_section(&[("env", "g", &[0x03, I32, 0x01])]));
    b.section(6, &global_section(&[(I32, 0x00, &[0x23, 0x00])]));
    assert_eq!(
        itasca::validate_module(&b.build()),
        Err(Error::MutableGlobalInConstExpr)
    );
}

#[test]
fn test_element_segment() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[], &[])]));
    b.section(3, &func_section(&[0]));
    b.section(4, &table_section(10, None));
    b.section(9, &element_section(&[(0, &[0x41, 0x00], &[0])]));
    b.section(10, &code_section(&[(&[], &[])]));
    itasca::validate_module(&b.build()).unwrap();
}

#[test]
fn test_element_segment_invalid_func() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[], &[])]));
    b.section(3, &func_section(&[0]));
    b.section(4, &table_section(10, None));
    b.section(9, &element_section(&[(0, &[0x41, 0x00], &[99])]));
    b.section(10, &code_section(&[(&[], &[])]));
    assert!(itasca::validate_module(&b.build()).is_err());
}

#[test]
fn test_element_segment_no_table() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[], &[])]));
    b.section(3, &func_section(&[0]));
    b.section(9, &element_section(&[(0, &[0x41, 0x00], &[0])]));
    b.section(10, &code_section(&[(&[], &[])]));
    assert!(itasca::validate_module(&b.build()).is_err());
}

#[test]
fn test_data_segment() {
    let mut b = ModuleBuilder::new();
    b.section(5, &memory_section(1, None));
    b.section(11, &data_section(&[(0, &[0x41, 0x00], b"hello")]));
    itasca::validate_module(&b.build()).unwrap();
}

#[test]
fn test_data_segment_no_memory() {
    let mut b = ModuleBuilder::new();
    b.section(11, &data_section(&[(0, &[0x41, 0x00], b"hello")]));
    assert!(itasca::validate_module(&b.build()).is_err());
}

#[test]
fn test_memory_limits_valid() {
    let mut b = ModuleBuilder::new();
    b.section(5, &memory_section(0, Some(65536)));
    itasca::validate_module(&b.build()).unwrap();
}

#[test]
fn test_memory_limits_min_exceeds_max() {
    let mut b = ModuleBuilder::new();
    b.section(5, &memory_section(10, Some(5)));
    assert_eq!(
        itasca::validate_module(&b.build()),
        Err(Error::LimitsOutOfRange)
    );
}

#[test]
fn test_memory_limits_exceeds_range() {
    let mut b = ModuleBuilder::new();
    b.section(5, &memory_section(65537, None));
    assert_eq!(
        itasca::validate_module(&b.build()),
        Err(Error::LimitsOutOfRange)
    );
}

#[test]
fn test_custom_section_ignored() {
    let mut b = ModuleBuilder::new();
    let mut custom = Vec::new();
    custom.push(0x04);
    custom.extend_from_slice(b"test");
    custom.extend_from_slice(b"payload");
    b.section(0, &custom);
    b.section(1, &type_section(&[(&[], &[])]));
    b.section(0, &custom); // custom sections can appear anywhere
    b.section(3, &func_section(&[0]));
    b.section(10, &code_section(&[(&[], &[])]));
    itasca::validate_module(&b.build()).unwrap();
}

/// Spec 5.5.3: the contents of a custom section start with a name, so the name
/// is checked even though nothing reads what follows it.
#[test]
fn test_custom_section_without_a_name() {
    let mut b = ModuleBuilder::new();
    b.section(0, &[]);
    assert_eq!(
        itasca::validate_module(&b.build()),
        Err(Error::Read(OpError::UnexpectedEof))
    );
}

#[test]
fn test_custom_section_with_invalid_utf8_name() {
    let mut b = ModuleBuilder::new();
    b.section(0, &[0x01, 0xff]);
    assert_eq!(itasca::validate_module(&b.build()), Err(Error::InvalidUtf8));
}

#[test]
fn test_custom_section_name_runs_past_its_end() {
    let mut b = ModuleBuilder::new();
    b.section(0, &[0x04, b'a']); // claims a four-byte name, one byte left
    b.section(1, &type_section(&[(&[], &[])]));
    assert_eq!(
        itasca::validate_module(&b.build()),
        Err(Error::SectionSizeMismatch)
    );
}

#[test]
fn test_custom_section_in_the_tail_is_checked_too() {
    let mut b = ModuleBuilder::new();
    b.section(5, &memory_section(1, None));
    b.section(11, &data_section(&[(0, &[0x41, 0x00], b"hi")]));
    b.section(0, &[0x01, 0xff]);
    assert_eq!(itasca::validate_module(&b.build()), Err(Error::InvalidUtf8));
}

#[test]
fn test_if_without_else() {
    let bytes = one_func_module(&[I32], &[], &[], &[0x20, 0x00, 0x04, 0x40, 0x01, 0x0B]);
    itasca::validate_module(&bytes).unwrap();
}

#[test]
fn test_if_result_without_else_fails() {
    // if (result i32) without else - else branch is empty, can't produce i32
    let bytes = one_func_module(
        &[I32],
        &[I32],
        &[],
        &[0x20, 0x00, 0x04, 0x7F, 0x41, 0x01, 0x0B],
    );
    assert!(itasca::validate_module(&bytes).is_err());
}

#[test]
fn test_unreachable_code_after_br() {
    let bytes = one_func_module(
        &[],
        &[I32],
        &[],
        &[
            0x02, 0x7F, // block (result i32)
            0x41, 0x01, // i32.const 1
            0x0C, 0x00, // br 0
            0x41, 0x02, // dead code
            0x1A, // drop (dead)
            0x0B, // end
        ],
    );
    itasca::validate_module(&bytes).unwrap();
}

#[test]
fn test_br_if_typing() {
    let bytes = one_func_module(
        &[I32],
        &[I32],
        &[],
        &[
            0x02, 0x7F, // block (result i32)
            0x20, 0x00, // local.get 0 (value)
            0x20, 0x00, // local.get 0 (condition)
            0x0D, 0x00, // br_if 0
            0x0B, // end
        ],
    );
    itasca::validate_module(&bytes).unwrap();
}

#[test]
fn test_loop_with_br() {
    let bytes = one_func_module(
        &[],
        &[],
        &[],
        &[
            0x03, 0x40, 0x0C, 0x00, 0x0B, // loop, br 0, end
        ],
    );
    itasca::validate_module(&bytes).unwrap();
}

#[test]
fn test_f64_add() {
    let bytes = one_func_module(&[F64, F64], &[F64], &[], &[0x20, 0x00, 0x20, 0x01, 0xA0]);
    itasca::validate_module(&bytes).unwrap();
}

#[test]
fn test_f32_mul() {
    let bytes = one_func_module(&[F32, F32], &[F32], &[], &[0x20, 0x00, 0x20, 0x01, 0x94]);
    itasca::validate_module(&bytes).unwrap();
}

#[test]
fn test_i32_wrap_i64() {
    let bytes = one_func_module(&[I64], &[I32], &[], &[0x20, 0x00, 0xA7]);
    itasca::validate_module(&bytes).unwrap();
}

#[test]
fn test_i64_extend_i32_s() {
    let bytes = one_func_module(&[I32], &[I64], &[], &[0x20, 0x00, 0xAC]);
    itasca::validate_module(&bytes).unwrap();
}

#[test]
fn test_f64_promote_f32() {
    let bytes = one_func_module(&[F32], &[F64], &[], &[0x20, 0x00, 0xBB]);
    itasca::validate_module(&bytes).unwrap();
}

#[test]
fn test_f32_reinterpret_i32() {
    let bytes = one_func_module(&[I32], &[F32], &[], &[0x20, 0x00, 0xBE]);
    itasca::validate_module(&bytes).unwrap();
}

#[test]
fn test_i64_reinterpret_f64() {
    let bytes = one_func_module(&[F64], &[I64], &[], &[0x20, 0x00, 0xBD]);
    itasca::validate_module(&bytes).unwrap();
}

#[test]
fn test_i64_load_store() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[I32, I64], &[I64])]));
    b.section(3, &func_section(&[0]));
    b.section(5, &memory_section(1, None));
    b.section(
        10,
        &code_section(&[(
            &[],
            &[
                0x20, 0x00, 0x20, 0x01, 0x37, 0x03, 0x00, // store
                0x20, 0x00, 0x29, 0x03, 0x00, // load
            ],
        )]),
    );
    itasca::validate_module(&b.build()).unwrap();
}

#[test]
fn test_i32_load8_store8() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[I32, I32], &[I32])]));
    b.section(3, &func_section(&[0]));
    b.section(5, &memory_section(1, None));
    b.section(
        10,
        &code_section(&[(
            &[],
            &[
                0x20, 0x00, 0x20, 0x01, 0x3A, 0x00, 0x00, // i32.store8
                0x20, 0x00, 0x2D, 0x00, 0x00, // i32.load8_u
            ],
        )]),
    );
    itasca::validate_module(&b.build()).unwrap();
}

#[test]
fn test_multiple_exports_different_names() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[], &[])]));
    b.section(3, &func_section(&[0, 0]));
    b.section(7, &export_section(&[("foo", 0x00, 0), ("bar", 0x00, 1)]));
    b.section(10, &code_section(&[(&[], &[]), (&[], &[])]));
    itasca::validate_module(&b.build()).unwrap();
}

#[test]
fn test_import_memory() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[I32], &[I32])]));
    b.section(2, &import_section(&[("env", "mem", &[0x02, 0x00, 0x01])]));
    b.section(3, &func_section(&[0]));
    b.section(10, &code_section(&[(&[], &[0x20, 0x00, 0x28, 0x02, 0x00])]));
    itasca::validate_module(&b.build()).unwrap();
}

#[test]
fn test_import_table() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[], &[])]));
    b.section(
        2,
        &import_section(&[("env", "tbl", &[0x01, 0x70, 0x00, 0x01])]),
    );
    b.section(3, &func_section(&[0]));
    b.section(10, &code_section(&[(&[], &[])]));
    itasca::validate_module(&b.build()).unwrap();
}

#[test]
fn test_multiple_memories_rejected() {
    let mut b = ModuleBuilder::new();
    let mut mem = Vec::new();
    mem.push(0x02); // count=2
    mem.extend_from_slice(&[0x00, 0x01, 0x00, 0x01]);
    b.section(5, &mem);
    assert_eq!(
        itasca::validate_module(&b.build()),
        Err(Error::MultipleMemories)
    );
}

#[test]
fn test_import_plus_defined_memory_rejected() {
    let mut b = ModuleBuilder::new();
    b.section(2, &import_section(&[("env", "mem", &[0x02, 0x00, 0x01])]));
    b.section(5, &memory_section(1, None));
    assert_eq!(
        itasca::validate_module(&b.build()),
        Err(Error::MultipleMemories)
    );
}

#[test]
fn test_multiple_types() {
    let mut b = ModuleBuilder::new();
    b.section(
        1,
        &type_section(&[
            (&[], &[]),
            (&[I32], &[I32]),
            (&[I32, I32], &[I32]),
            (&[F64], &[F64]),
        ]),
    );
    b.section(3, &func_section(&[0, 1, 2, 3]));
    b.section(
        10,
        &code_section(&[
            (&[], &[]),
            (&[], &[0x20, 0x00]),
            (&[], &[0x20, 0x00, 0x20, 0x01, 0x6A]),
            (&[], &[0x20, 0x00]),
        ]),
    );
    itasca::validate_module(&b.build()).unwrap();
}

#[test]
fn test_func_code_count_mismatch() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[], &[])]));
    b.section(3, &func_section(&[0, 0]));
    b.section(10, &code_section(&[(&[], &[])]));
    assert_eq!(
        itasca::validate_module(&b.build()),
        Err(Error::FuncCodeMismatch)
    );
}

#[test]
fn test_unknown_type_index_in_func() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[], &[])]));
    b.section(3, &func_section(&[99]));
    b.section(10, &code_section(&[(&[], &[])]));
    // Caught while decoding, not while validating: the function index space is
    // built by the decoder, and it cannot resolve type 99.
    assert_eq!(
        itasca::validate_module(&b.build()),
        Err(Error::UnknownType(99))
    );
}

#[test]
fn test_unknown_type_index_in_import() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[], &[])]));
    b.section(2, &import_section(&[("m", "f", &[0x00, 99])]));
    assert_eq!(
        itasca::validate_module(&b.build()),
        Err(Error::UnknownType(99))
    );
}

#[test]
fn test_stack_extra_values_rejected() {
    let bytes = one_func_module(&[], &[I32], &[], &[0x41, 0x01, 0x41, 0x02]);
    assert!(itasca::validate_module(&bytes).is_err());
}

#[test]
fn test_drop_on_empty_stack() {
    let bytes = one_func_module(&[], &[], &[], &[0x1A]);
    assert!(itasca::validate_module(&bytes).is_err());
}

#[test]
fn test_decode_f32_const() {
    let bytes = one_func_module(&[], &[F32], &[], &[0x43, 0x00, 0x00, 0xC0, 0x3F]);
    itasca::validate_module(&bytes).unwrap();
}

#[test]
fn test_unreachable_with_dead_const_rejected() {
    // Function [] -> [], body = [unreachable, i32.const 0]
    // Dead code after unreachable leaves i32 on stack with unr=true.
    // This is invalid: stack must be empty after consuming results.
    let bytes = one_func_module(&[], &[], &[], &[0x00, 0x41, 0x00]); // unreachable, i32.const 0
    assert!(itasca::validate_module(&bytes).is_err());
}

#[test]
fn test_decode_f64_const() {
    let bytes = one_func_module(
        &[],
        &[F64],
        &[],
        &[0x44, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xF8, 0x3F],
    );
    itasca::validate_module(&bytes).unwrap();
}

// ---- The environment / code / tail split ----

/// A custom section with the given name and payload.
fn custom_section(name: &str, payload: &[u8]) -> Vec<u8> {
    let mut contents = Vec::new();
    contents.extend_from_slice(&leb128_u32(name.len() as u32));
    contents.extend_from_slice(name.as_bytes());
    contents.extend_from_slice(payload);
    contents
}

#[test]
fn test_code_section_without_function_section() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[], &[])]));
    b.section(10, &code_section(&[(&[], &[])]));
    assert_eq!(
        itasca::validate_module(&b.build()),
        Err(Error::FuncCodeMismatch)
    );
}

/// Reported apart from a count mismatch, because a consumer reading a module as
/// it arrives has to tell "the code section is not here yet" from "the code
/// section is wrong".
#[test]
fn test_function_section_without_code_section() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[], &[])]));
    b.section(3, &func_section(&[0]));
    assert_eq!(
        itasca::validate_module(&b.build()),
        Err(Error::MissingCodeSection)
    );
}

#[test]
fn test_data_section_before_code_section() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[], &[])]));
    b.section(3, &func_section(&[0]));
    b.section(5, &memory_section(1, None));
    b.section(11, &data_section(&[(0, &[0x41, 0x00], b"hi")]));
    b.section(10, &code_section(&[(&[], &[])]));
    // The data section ends the environment, so the code section is missing and
    // then the tail meets a section id it will not take.
    assert!(itasca::validate_module(&b.build()).is_err());
}

#[test]
fn test_custom_sections_around_the_code_section() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[], &[])]));
    b.section(3, &func_section(&[0]));
    b.section(5, &memory_section(1, None));
    b.section(0, &custom_section("before.code", b"x"));
    b.section(10, &code_section(&[(&[], &[])]));
    b.section(0, &custom_section("before.data", b"y"));
    b.section(11, &data_section(&[(0, &[0x41, 0x00], b"hi")]));
    b.section(0, &custom_section("after.data", b"z"));
    let m = itasca::validate_module(&b.build()).unwrap();
    assert_eq!(m.tail.data.len(), 1);
}

#[test]
fn test_two_data_sections_are_rejected() {
    let mut b = ModuleBuilder::new();
    b.section(5, &memory_section(1, None));
    b.section(11, &data_section(&[(0, &[0x41, 0x00], b"a")]));
    b.section(11, &data_section(&[(0, &[0x41, 0x00], b"b")]));
    assert_eq!(
        itasca::validate_module(&b.build()),
        Err(Error::SectionOutOfOrder)
    );
}

#[test]
fn test_element_offset_reads_an_imported_global() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[], &[])]));
    // An immutable imported i32 global, which is the only thing an initialiser
    // may name.
    b.section(2, &import_section(&[("env", "base", &[0x03, 0x7F, 0x00])]));
    b.section(3, &func_section(&[0]));
    b.section(4, &table_section(1, None));
    b.section(9, &element_section(&[(0, &[0x23, 0x00], &[0])]));
    b.section(10, &code_section(&[(&[], &[])]));
    let m = itasca::validate_module(&b.build()).unwrap();
    assert_eq!(m.env.num_imported_globals, 1);
    assert_eq!(m.env.elements[0].offset, ConstExpr::GlobalGet(0));
}

#[test]
fn test_element_offset_cannot_read_a_defined_global() {
    let mut b = ModuleBuilder::new();
    b.section(4, &table_section(1, None));
    b.section(6, &global_section(&[(I32, 0x00, &[0x41, 0x00])]));
    b.section(9, &element_section(&[(0, &[0x23, 0x00], &[])]));
    assert_eq!(
        itasca::validate_module(&b.build()),
        Err(Error::MutableGlobalInConstExpr)
    );
}

// ---- Names (spec 5.2.4) ----

/// An import section built from raw name bytes, so a test can write a name
/// that `&str` could not hold.
fn import_section_raw(module: &[u8], name: &[u8], desc: &[u8]) -> Vec<u8> {
    let mut contents = Vec::new();
    contents.push(0x01);
    contents.extend_from_slice(&leb128_u32(module.len() as u32));
    contents.extend_from_slice(module);
    contents.extend_from_slice(&leb128_u32(name.len() as u32));
    contents.extend_from_slice(name);
    contents.extend_from_slice(desc);
    contents
}

#[test]
fn test_import_name_must_be_utf8() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[], &[])]));
    // 0xC0 0x80 is the overlong encoding of U+0000, which UTF-8 forbids.
    b.section(2, &import_section_raw(b"env", &[0xC0, 0x80], &[0x00, 0x00]));
    assert_eq!(itasca::validate_module(&b.build()), Err(Error::InvalidUtf8));
}

#[test]
fn test_export_name_must_be_utf8() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[], &[])]));
    b.section(3, &func_section(&[0]));
    // A lone surrogate, U+D800, encoded as if it were a scalar value.
    let mut contents = Vec::new();
    contents.push(0x01);
    contents.extend_from_slice(&leb128_u32(3));
    contents.extend_from_slice(&[0xED, 0xA0, 0x80]);
    contents.push(0x00);
    contents.push(0x00);
    b.section(7, &contents);
    b.section(10, &code_section(&[(&[], &[])]));
    assert_eq!(itasca::validate_module(&b.build()), Err(Error::InvalidUtf8));
}

#[test]
fn test_multibyte_names_are_accepted() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[], &[])]));
    b.section(3, &func_section(&[0]));
    b.section(7, &export_section(&[("\u{e9}\u{4e2d}\u{1f600}", 0x00, 0)]));
    b.section(10, &code_section(&[(&[], &[])]));
    itasca::validate_module(&b.build()).unwrap();
}

// ---- Driving the code section one entry at a time ----

#[test]
fn test_validate_code_entry_matches_validate_code() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[], &[I32])]));
    b.section(3, &func_section(&[0, 0]));
    b.section(
        10,
        &code_section(&[(&[], &[0x41, 0x07]), (&[(1, I32)], &[0x20, 0x00])]),
    );
    let bytes = b.build();

    let (env, code_pos) = itasca::module::validate_env(&bytes).unwrap();
    assert_eq!(env.func_type_indices.len(), 2);

    // Skip the code section's header and entry count by hand, then drive the
    // entries the way a consumer that compiles them in parallel would.
    let header_len = 1 + 1; // section id, and a one-byte size for this module
    let count_len = 1;
    let mut pos = code_pos + header_len + count_len;
    let mut i = 0;
    while i < env.func_type_indices.len() {
        pos = itasca::module::validate_code_entry(&bytes, pos, &env, i).unwrap();
        i += 1;
    }

    // The same position validate_code would have stopped at.
    assert_eq!(
        pos,
        itasca::module::validate_code(&bytes, code_pos, &env).unwrap()
    );
    assert!(itasca::module::validate_tail(&bytes, pos, &env)
        .unwrap()
        .data
        .is_empty());
}

#[test]
fn test_too_many_locals_is_rejected() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[], &[])]));
    b.section(3, &func_section(&[0]));
    b.section(10, &code_section(&[(&[(1_000_000, I32)], &[])]));
    assert_eq!(
        itasca::validate_module(&b.build()),
        Err(Error::TooManyLocals)
    );
}

#[test]
fn test_multi_result_type_is_rejected() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[], &[I32, I32])]));
    assert_eq!(
        itasca::validate_module(&b.build()),
        Err(Error::TooManyResults)
    );
}

#[test]
fn test_section_size_must_match_its_contents() {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&[0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00]);
    // A type section whose size prefix claims one byte more than it holds.
    let contents = type_section(&[(&[], &[])]);
    bytes.push(1);
    bytes.extend_from_slice(&leb128_u32(contents.len() as u32 + 1));
    bytes.extend_from_slice(&contents);
    bytes.push(0x00);
    assert_eq!(
        itasca::validate_module(&bytes),
        Err(Error::SectionSizeMismatch)
    );
}

/// `MAX_LOCALS` caps what a function *declares*, not its whole frame, so a
/// parameter does not count against it. That is a deliberate divergence from
/// SpiderMonkey, whose `MaxLocals` counts parameters too, and it is pinned here
/// because it looks like an oversight and is not one.
///
/// The cap exists to bound what `decode_locals` allocates, and it does. Making
/// it cover the frame would import an implementation limit the specification
/// does not have, and would cost a weaker completeness theorem to do it: the
/// bound would have to become a joint condition on a function's type and its
/// body, carried through `repr_module_fit` to the top. SpiderMonkey has to
/// enforce its own limits on its own side anyway -- `MaxParams` is a
/// `MOZ_RELEASE_ASSERT` in `WasmTypeDef.h`, so nothing else can be relied on to
/// keep it -- and this belongs with those.
#[test]
fn test_the_locals_cap_is_on_the_declaration_not_the_frame() {
    let build = |params: &[u8], locals: u32| {
        let mut b = ModuleBuilder::new();
        b.section(1, &type_section(&[(params, &[])]));
        b.section(3, &func_section(&[0]));
        b.section(10, &code_section(&[(&[(locals, I32)], &[])]));
        b.build()
    };

    // The declaration's own cap.
    assert!(itasca::validate_module(&build(&[], 50_000)).is_ok());
    assert_eq!(
        itasca::validate_module(&build(&[], 50_001)),
        Err(Error::TooManyLocals)
    );

    // A parameter buys no less room, which is where SpiderMonkey would differ:
    // 1 + 50000 slots is over its MaxLocals and within our cap.
    assert!(itasca::validate_module(&build(&[I32], 50_000)).is_ok());
}

/// A visitor that records every custom section it is shown, which is what a
/// consumer that wants them does.
#[derive(Default)]
struct Customs(Vec<itasca::types::CustomSection>);

impl itasca::module::ModuleVisitor for Customs {
    fn on_custom_section(&mut self, s: itasca::types::CustomSection) -> itasca::VisitResult {
        self.0.push(s);
        Ok(())
    }
}

/// The name a custom section reports, resolved in the bytes the decoder that
/// reported it was handed.
fn custom_name<'a>(bytes: &'a [u8], c: &itasca::types::CustomSection) -> &'a [u8] {
    &bytes[c.payload_start - c.name_len..c.payload_start]
}

#[test]
fn test_custom_sections_are_reported_with_their_ranges() {
    // Two customs, one before the type section and one at the end, plus a
    // nameless one to check that an empty name is a name.
    let mut b = ModuleBuilder::new();
    let custom = |name: &[u8], payload: &[u8]| {
        let mut s = leb128_u32(name.len() as u32);
        s.extend_from_slice(name);
        s.extend_from_slice(payload);
        s
    };
    b.section(0, &custom(b"first", &[1, 2, 3]));
    b.section(1, &type_section(&[(&[], &[])]));
    b.section(0, &custom(b"", &[]));
    b.section(0, &custom(b"last", &[9]));
    let bytes = b.build();

    assert!(itasca::validate_module(&bytes).is_ok());

    // No code section, so the environment ran to the end and saw all three.
    let mut seen = Customs::default();
    itasca::module::validate_env_with(&bytes, &mut seen).unwrap();
    let names: Vec<&[u8]> = seen.0.iter().map(|c| custom_name(&bytes, c)).collect();
    assert_eq!(names, vec![&b"first"[..], &b""[..], &b"last"[..]]);

    // The ranges are into the module, and hold what was put in them.
    let payload = |c: &itasca::types::CustomSection| &bytes[c.payload_start..c.payload_end];
    assert_eq!(payload(&seen.0[0]), &[1, 2, 3]);
    assert_eq!(payload(&seen.0[1]), &[] as &[u8]);
    assert_eq!(payload(&seen.0[2]), &[9]);
}

/// A custom section is legal between any two others and the code section
/// cannot hold one, so one walk reports the ones before it and the other the
/// ones after. The same visitor takes both, which is why it is one trait.
#[test]
fn test_custom_sections_are_split_across_the_code_section() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[], &[])]));
    b.section(3, &func_section(&[0]));
    b.section(0, &custom_section("before.code", b"x"));
    b.section(10, &code_section(&[(&[], &[])]));
    b.section(0, &custom_section("after.code", b"y"));
    let bytes = b.build();

    let mut seen = Customs::default();
    let (env, code_pos) = itasca::module::validate_env_with(&bytes, &mut seen).unwrap();
    assert_eq!(
        seen.0
            .iter()
            .map(|c| custom_name(&bytes, c))
            .collect::<Vec<_>>(),
        vec![&b"before.code"[..]]
    );

    let tail_pos = itasca::module::code_section(&bytes, code_pos, &env)
        .unwrap()
        .unwrap()
        .end;

    // Carrying on with the same visitor gives the module's customs in order.
    itasca::module::validate_tail_with(&bytes, tail_pos, &env, &mut seen).unwrap();
    assert_eq!(
        seen.0
            .iter()
            .map(|c| custom_name(&bytes, c))
            .collect::<Vec<_>>(),
        vec![&b"before.code"[..], &b"after.code"[..]]
    );
    let after = seen.0[1];
    assert_eq!(&bytes[after.payload_start..after.payload_end], b"y");

    // Held in pieces, the tail's region does not begin with the module's
    // header and its positions are into the region.
    let region = &bytes[tail_pos..];
    let mut piece = Customs::default();
    itasca::module::validate_tail_with(region, 0, &env, &mut piece).unwrap();
    assert_eq!(
        piece
            .0
            .iter()
            .map(|c| custom_name(region, c))
            .collect::<Vec<_>>(),
        vec![&b"after.code"[..]]
    );
    assert_eq!(piece.0[0].payload_start + tail_pos, after.payload_start);
}

/// A consumer that declines stops the decode, and says so as a decline rather
/// than as a verdict about the module.
#[test]
fn test_a_declining_module_consumer_stops_the_decode() {
    struct Refuser;
    impl itasca::module::ModuleVisitor for Refuser {
        fn on_custom_section(&mut self, _s: itasca::types::CustomSection) -> itasca::VisitResult {
            Err(itasca::VisitError::OutOfMemory)
        }
    }

    let mut b = ModuleBuilder::new();
    b.section(0, &custom_section("nope", b""));
    b.section(1, &type_section(&[(&[], &[])]));
    let bytes = b.build();

    // The module itself is fine.
    assert!(itasca::validate_module(&bytes).is_ok());
    assert_eq!(
        itasca::module::validate_env_with(&bytes, &mut Refuser).unwrap_err(),
        Error::Visitor(itasca::VisitError::OutOfMemory)
    );
}

#[test]
fn test_a_module_with_no_custom_sections_reports_none() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[], &[])]));
    let bytes = b.build();
    let mut seen = Customs::default();
    itasca::module::validate_env_with(&bytes, &mut seen).unwrap();
    assert!(seen.0.is_empty());
}

/// A consumer that records each entry it is shown and validates it where it
/// stands, which is what a compiler does except for the compiling.
#[derive(Default)]
struct Entries {
    seen: Vec<(usize, usize, usize, usize)>,
    waits: Vec<usize>,
}

impl itasca::module::CodeVisitor for Entries {
    fn on_need_bytes(&mut self, end: usize) -> Result<(), Error> {
        self.waits.push(end);
        Ok(())
    }

    fn on_code_entry(
        &mut self,
        data: &[u8],
        env: &itasca::module::Env,
        index: usize,
        entry_pos: usize,
        contents_start: usize,
        entry_end: usize,
    ) -> Result<(), Error> {
        self.seen
            .push((index, entry_pos, contents_start, entry_end));
        itasca::module::validate_code_entry(data, entry_pos, env, index)?;
        Ok(())
    }
}

/// The driven walk and `validate_code` accept the same bytes and land on the
/// same position, and the entries the consumer was shown tile the section.
#[test]
fn test_validate_code_with_agrees_with_validate_code() {
    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[], &[]), (&[I32], &[I32])]));
    b.section(3, &func_section(&[0, 1, 0]));
    b.section(
        10,
        &code_section(&[(&[], &[]), (&[(1, I64)], &[0x20, 0x00]), (&[], &[0x01])]),
    );
    let bytes = b.build();

    let (env, code_pos) = itasca::module::validate_env(&bytes).unwrap();
    let cs = itasca::module::code_section(&bytes, code_pos, &env)
        .unwrap()
        .unwrap();

    let mut seen = Entries::default();
    let next = itasca::module::validate_code_with(&bytes, code_pos, &env, &mut seen).unwrap();
    assert_eq!(
        next,
        itasca::module::validate_code(&bytes, code_pos, &env).unwrap()
    );
    assert_eq!(next, cs.end);

    // Three entries, in order, and their extents tile the section exactly.
    assert_eq!(seen.seen.len(), 3);
    let mut q = cs.entries;
    for (i, &(index, entry_pos, contents, end)) in seen.seen.iter().enumerate() {
        assert_eq!(index, i);
        assert_eq!(entry_pos, q);
        assert!(entry_pos < contents && contents <= end);
        q = end;
    }
    assert_eq!(q, cs.end);

    // Every read was waited for first, and never past the section's end.
    assert!(!seen.waits.is_empty());
    assert!(seen.waits.iter().all(|&w| w >= code_pos));
}

/// A consumer that declines stops the walk. Nothing about the bytes changed:
/// the same section is fine when validated in place.
#[test]
fn test_a_declining_code_consumer_stops_the_walk() {
    struct Refuser;
    impl itasca::module::CodeVisitor for Refuser {
        fn on_code_entry(
            &mut self,
            _data: &[u8],
            _env: &itasca::module::Env,
            _index: usize,
            _entry_pos: usize,
            _contents_start: usize,
            _entry_end: usize,
        ) -> Result<(), Error> {
            Err(Error::Visitor(itasca::VisitError::OutOfMemory))
        }
    }

    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[], &[])]));
    b.section(3, &func_section(&[0]));
    b.section(10, &code_section(&[(&[], &[])]));
    let bytes = b.build();

    let (env, code_pos) = itasca::module::validate_env(&bytes).unwrap();
    assert!(itasca::module::validate_code(&bytes, code_pos, &env).is_ok());
    assert_eq!(
        itasca::module::validate_code_with(&bytes, code_pos, &env, &mut Refuser).unwrap_err(),
        Error::Visitor(itasca::VisitError::OutOfMemory)
    );
}

/// One consumer for a whole module: it hears the custom sections on both sides
/// of the code section and validates every entry it is shown, which is the
/// shape a compiler drives.
#[derive(Default)]
struct Driver {
    customs: Vec<itasca::types::CustomSection>,
    entries: Vec<(usize, usize)>,
}

impl itasca::module::ModuleVisitor for Driver {
    fn on_custom_section(&mut self, s: itasca::types::CustomSection) -> itasca::VisitResult {
        self.customs.push(s);
        Ok(())
    }
}

impl itasca::module::CodeVisitor for Driver {
    fn on_code_entry(
        &mut self,
        data: &[u8],
        env: &itasca::module::Env,
        index: usize,
        entry_pos: usize,
        _contents_start: usize,
        entry_end: usize,
    ) -> Result<(), Error> {
        self.entries.push((entry_pos, entry_end));
        itasca::module::validate_code_entry(data, entry_pos, env, index)?;
        Ok(())
    }
}

/// The driven whole-module run is the plain one: same verdict, same module,
/// and the consumer saw the sections in module order.
#[test]
fn test_validate_module_with_agrees_with_validate_module() {
    let mut b = ModuleBuilder::new();
    b.section(0, &custom_section("before", b"a"));
    b.section(1, &type_section(&[(&[], &[])]));
    b.section(3, &func_section(&[0]));
    b.section(10, &code_section(&[(&[], &[])]));
    b.section(0, &custom_section("after", b"b"));
    let bytes = b.build();

    let mut d = Driver::default();
    let driven = itasca::module::validate_module_with(&bytes, &mut d).unwrap();
    let plain = itasca::validate_module(&bytes).unwrap();
    assert_eq!(driven, plain);

    // Both sides of the code section, in module order.
    let names: Vec<&[u8]> = d
        .customs
        .iter()
        .map(|c| &bytes[c.payload_start - c.name_len..c.payload_start])
        .collect();
    assert_eq!(names, vec![&b"before"[..], &b"after"[..]]);
    assert_eq!(d.entries.len(), 1);
}

/// A consumer that refuses an entry stops the whole module, and says so as a
/// decline rather than as a verdict about the bytes.
#[test]
fn test_a_declining_driver_stops_the_module() {
    struct Refuser;
    impl itasca::module::ModuleVisitor for Refuser {}
    impl itasca::module::CodeVisitor for Refuser {
        fn on_code_entry(
            &mut self,
            _data: &[u8],
            _env: &itasca::module::Env,
            _index: usize,
            _entry_pos: usize,
            _contents_start: usize,
            _entry_end: usize,
        ) -> Result<(), Error> {
            Err(Error::Visitor(itasca::VisitError::OutOfMemory))
        }
    }

    let mut b = ModuleBuilder::new();
    b.section(1, &type_section(&[(&[], &[])]));
    b.section(3, &func_section(&[0]));
    b.section(10, &code_section(&[(&[], &[])]));
    let bytes = b.build();

    assert!(itasca::validate_module(&bytes).is_ok());
    assert_eq!(
        itasca::module::validate_module_with(&bytes, &mut Refuser).unwrap_err(),
        Error::Visitor(itasca::VisitError::OutOfMemory)
    );
}

/// Pushes past `ValsStack`'s 32-entry inline capacity and back down again,
/// so the overflow `Vec` and the boundary between it and the inline array
/// both get exercised, not just the common case.
#[test]
fn test_operand_stack_past_inline_capacity() {
    let mut body = Vec::new();
    for _ in 0..40 {
        body.extend_from_slice(&[0x41, 0x01]); // i32.const 1
    }
    for _ in 0..40 {
        body.push(0x1A); // drop
    }
    let bytes = one_func_module(&[], &[], &[], &body);
    itasca::validate_module(&bytes).unwrap();
}

/// Declares past `LocalsStack`'s 32-entry inline capacity, then reads the
/// last one, so both the overflow `Vec` and the boundary between it and the
/// inline array are exercised for locals too.
#[test]
fn test_locals_past_inline_capacity() {
    let body = [0x20, 39, 0x1A]; // local.get 39, drop
    let bytes = one_func_module(&[], &[], &[(40, I32)], &body);
    itasca::validate_module(&bytes).unwrap();
}

/// Nests past `CtrlsStack`'s 16-entry inline capacity, then `br`s out from
/// the innermost frame to the outermost, so label resolution and frame
/// popping both cross the inline/overflow boundary.
#[test]
fn test_control_stack_past_inline_capacity() {
    let mut body = Vec::new();
    for _ in 0..20 {
        body.extend_from_slice(&[0x02, 0x40]); // block (empty)
    }
    body.extend_from_slice(&[0x0C, 19]); // br 19 (out to the outermost)
    for _ in 0..20 {
        body.push(0x0B); // end
    }
    let bytes = one_func_module(&[], &[], &[], &body);
    itasca::validate_module(&bytes).unwrap();
}
