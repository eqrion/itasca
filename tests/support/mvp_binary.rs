//! Rewrites element and data sections from the binary encoding `wasm-encoder`
//! (used by both `wast` and `wasm-smith`) always emits into the encoding the
//! actual Wasm 1.0 spec defines.
//!
//! The bulk-memory proposal replaced the original flag-less element/data
//! segment encoding with a flags-prefixed one (passive segments, explicit
//! table/memory indices, `elemkind`/`reftype` bytes). Every current
//! `wasm-encoder`-based tool emits only the new encoding, even for content
//! that is semantically Wasm 1.0 and uses none of what the flags add. veriwasm
//! decodes the actual Wasm 1.0 grammar (no flags), matching the W3C REC, so
//! bytes from `wasm-encoder` need translating before veriwasm can be tested
//! against them.
//!
//! Wasm 1.0 has at most one table and one memory, so every segment it can
//! express targets index 0 and is active (never passive or declarative) -
//! exactly the flag values `0` and `2` cover. Translation is section-local:
//! walk the module's sections, rewrite element (id 9) and data (id 11)
//! sections, and copy everything else through untouched.

// The message is read by `examples/wast_extract.rs`; fuzz targets only match
// on `Err(_)`, so this field looks unused from their compilation.
#[allow(dead_code)]
pub struct Untranslatable(pub String);

struct Reader<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> Reader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Reader { bytes, pos: 0 }
    }

    fn at_end(&self) -> bool {
        self.pos == self.bytes.len()
    }

    fn read_u8(&mut self) -> Result<u8, Untranslatable> {
        let b = *self
            .bytes
            .get(self.pos)
            .ok_or_else(|| Untranslatable("unexpected end of section".to_string()))?;
        self.pos += 1;
        Ok(b)
    }

    fn read_bytes(&mut self, n: usize) -> Result<&'a [u8], Untranslatable> {
        let out = self
            .bytes
            .get(self.pos..self.pos + n)
            .ok_or_else(|| Untranslatable("unexpected end of section".to_string()))?;
        self.pos += n;
        Ok(out)
    }

    fn read_u32_leb(&mut self) -> Result<u32, Untranslatable> {
        let mut result: u32 = 0;
        let mut shift = 0;
        loop {
            let byte = self.read_u8()?;
            result |= ((byte & 0x7f) as u32) << shift;
            if byte & 0x80 == 0 {
                return Ok(result);
            }
            shift += 7;
        }
    }

    /// Skips one LEB128-encoded operand (signed or unsigned; the encoding of
    /// either is only distinguished by how the value is interpreted, not by
    /// its length) and returns its raw bytes.
    fn skip_leb(&mut self) -> Result<&'a [u8], Untranslatable> {
        let start = self.pos;
        loop {
            let byte = self.read_u8()?;
            if byte & 0x80 == 0 {
                return Ok(&self.bytes[start..self.pos]);
            }
        }
    }

    /// Reads a Wasm 1.0 constant expression verbatim: one
    /// `i32.const`/`i64.const`/`f32.const`/`f64.const`/`global.get`
    /// instruction followed by `end` (0x0b).
    fn read_const_expr(&mut self) -> Result<&'a [u8], Untranslatable> {
        let start = self.pos;
        let opcode = self.read_u8()?;
        match opcode {
            0x41 | 0x42 | 0x23 => {
                self.skip_leb()?;
            }
            0x43 => {
                self.read_bytes(4)?;
            }
            0x44 => {
                self.read_bytes(8)?;
            }
            _ => {
                return Err(Untranslatable(format!(
                    "const expr opcode 0x{opcode:02x} is not part of Wasm 1.0"
                )))
            }
        }
        let end = self.read_u8()?;
        if end != 0x0b {
            return Err(Untranslatable("const expr missing `end`".to_string()));
        }
        Ok(&self.bytes[start..self.pos])
    }
}

fn write_u32_leb(out: &mut Vec<u8>, mut value: u32) {
    loop {
        let byte = (value & 0x7f) as u8;
        value >>= 7;
        if value == 0 {
            out.push(byte);
            return;
        }
        out.push(byte | 0x80);
    }
}

/// The Wasm 1.0 encoding of an active segment's `funcidx*`/byte-vector tail:
/// index count, then each raw index/byte, copied straight from the flags
/// encoding.
fn copy_u32_vec(r: &mut Reader, out: &mut Vec<u8>) -> Result<(), Untranslatable> {
    let count = r.read_u32_leb()?;
    write_u32_leb(out, count);
    for _ in 0..count {
        out.extend_from_slice(r.skip_leb()?);
    }
    Ok(())
}

fn transcode_elem_section(content: &[u8]) -> Result<Vec<u8>, Untranslatable> {
    let mut r = Reader::new(content);
    let mut out = Vec::new();
    let count = r.read_u32_leb()?;
    write_u32_leb(&mut out, count);
    for _ in 0..count {
        let flag = r.read_u32_leb()?;
        match flag {
            // Active, table 0 implied, funcref elemkind implied, vec(funcidx).
            0 => {
                write_u32_leb(&mut out, 0); // table_idx, explicit in Wasm 1.0
                out.extend_from_slice(r.read_const_expr()?);
                copy_u32_vec(&mut r, &mut out)?;
            }
            // Active, explicit table index, elemkind byte, vec(funcidx).
            2 => {
                let table_idx = r.read_u32_leb()?;
                write_u32_leb(&mut out, table_idx);
                out.extend_from_slice(r.read_const_expr()?);
                let elemkind = r.read_u8()?;
                if elemkind != 0x00 {
                    return Err(Untranslatable(format!(
                        "elemkind 0x{elemkind:02x} is not part of Wasm 1.0"
                    )));
                }
                copy_u32_vec(&mut r, &mut out)?;
            }
            _ => {
                return Err(Untranslatable(format!(
                    "element segment flag {flag} is not part of Wasm 1.0"
                )))
            }
        }
    }
    if !r.at_end() {
        return Err(Untranslatable(
            "trailing bytes in element section".to_string(),
        ));
    }
    Ok(out)
}

fn transcode_data_section(content: &[u8]) -> Result<Vec<u8>, Untranslatable> {
    let mut r = Reader::new(content);
    let mut out = Vec::new();
    let count = r.read_u32_leb()?;
    write_u32_leb(&mut out, count);
    for _ in 0..count {
        let flag = r.read_u32_leb()?;
        match flag {
            // Active, memory 0 implied.
            0 => {
                write_u32_leb(&mut out, 0); // mem_idx, explicit in Wasm 1.0
                out.extend_from_slice(r.read_const_expr()?);
                let n = r.read_u32_leb()?;
                write_u32_leb(&mut out, n);
                out.extend_from_slice(r.read_bytes(n as usize)?);
            }
            // Active, explicit memory index.
            2 => {
                let mem_idx = r.read_u32_leb()?;
                write_u32_leb(&mut out, mem_idx);
                out.extend_from_slice(r.read_const_expr()?);
                let n = r.read_u32_leb()?;
                write_u32_leb(&mut out, n);
                out.extend_from_slice(r.read_bytes(n as usize)?);
            }
            _ => {
                return Err(Untranslatable(format!(
                    "data segment flag {flag} is not part of Wasm 1.0"
                )))
            }
        }
    }
    if !r.at_end() {
        return Err(Untranslatable("trailing bytes in data section".to_string()));
    }
    Ok(out)
}

/// Rewrites `wasm-encoder`-produced bytes into genuine Wasm 1.0 encoding.
/// Fails if a section uses something Wasm 1.0 cannot express (a passive or
/// declarative segment, a non-`funcref` elemkind, and so on) rather than
/// guessing; callers should treat that as "not applicable to Wasm 1.0",
/// same as any other module that fails to encode.
pub fn normalize_to_wasm1(bytes: &[u8]) -> Result<Vec<u8>, Untranslatable> {
    const HEADER_LEN: usize = 8;
    if bytes.len() < HEADER_LEN || &bytes[0..4] != b"\0asm" {
        return Err(Untranslatable("not a Wasm binary".to_string()));
    }
    let mut out = Vec::with_capacity(bytes.len());
    out.extend_from_slice(&bytes[0..HEADER_LEN]);

    let mut r = Reader::new(&bytes[HEADER_LEN..]);
    while !r.at_end() {
        let id = r.read_u8()?;
        let size = r.read_u32_leb()?;
        let content = r.read_bytes(size as usize)?;
        let new_content = match id {
            9 => transcode_elem_section(content)?,
            11 => transcode_data_section(content)?,
            _ => content.to_vec(),
        };
        out.push(id);
        write_u32_leb(&mut out, new_content.len() as u32);
        out.extend_from_slice(&new_content);
    }
    Ok(out)
}
