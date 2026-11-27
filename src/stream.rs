//! Streaming module validation with bounded, independently scheduled workers.
//!
//! `validate_streaming` decodes the environment, issues `StreamingBatch` work, validates
//! the tail, and retires every outstanding batch before accepting. Workers may
//! complete in any order. `StreamingSource` defines the byte-coherence obligation;
//! `StreamingVisitor` defines callback order and worker ownership.
//!
//! The source and environment must outlive every worker. Invocation IDs must be
//! unique among batches that can reach the same scheduler. Returned workers must
//! derive from the corresponding issued batches through their batch operations.
//! Callbacks must return normally for termination and accept for completeness.
//! Only a successful driver result certifies whole-module validity.

use crate::limits::{add_offset, MAX_CODE_HEADER_BYTES, MAX_LEB_BYTES};
use crate::metadata::{self, SECTION_CODE, SECTION_DATA_COUNT};
use crate::{CodeMetadata, Error, ModuleMetadata, OpError, OpVisitor};
use alloc::sync::Arc;
use alloc::vec::Vec;

/// A module validation or streaming-protocol result.
pub type Result<T> = core::result::Result<T, Error>;

/// The target batch size and maximum number of outstanding batches.
///
/// Both fields must be positive; the driver rejects zero values.
pub struct StreamingConfig {
    /// The target entry-content bytes per batch, including locals. One entry may
    /// exceed it.
    pub batch_bytes: usize,
    /// The maximum number of submitted batches awaiting return from the visitor.
    pub max_batches: usize,
}

/// A coherent module source split into environment, code, and tail regions.
///
/// The canonical split starts the code region at the first section whose ID is at
/// least 10. That region contains the complete code section if present, otherwise
/// it is empty. The tail follows it; preceding bytes belong to the environment.
/// If no such section exists, all bytes belong to the environment.
///
/// Regions may use separate allocations. Every successful read must agree with
/// the same fixed logical bytes; immutable Rust borrows alone do not ensure
/// coherence across calls. Read errors may reject otherwise valid input.
pub trait StreamingSource {
    /// Returns the complete environment region, including the module header.
    fn environment(&self) -> Result<&[u8]>;

    /// Returns the fixed length of the code region before its bytes are
    /// requested.
    fn code_len(&self) -> usize;

    /// Waits for and returns the exact code-region range `start..end`.
    ///
    /// The driver requests `start <= end <= code_len()`. Successful reads must
    /// agree with the same logical code bytes, including overlapping reads.
    fn code(&self, start: usize, end: usize) -> Result<&[u8]>;

    /// Waits for end of input and returns the complete tail region.
    fn tail(&self) -> Result<&[u8]>;
}

/// The source region for subsequent custom-section offsets.
#[derive(Clone, Copy)]
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
pub enum StreamingRegion {
    Environment,
    Tail,
}

/// Receives module events, submits batches and collects them in completion order.
/// A batch owns a shared metadata handle and borrows its bytes from the source.
pub trait StreamingVisitor<'a>: metadata::ModuleVisitor {
    fn custom_region(&mut self, region: StreamingRegion);

    /// The prefix and code header are valid. Data segments are still pending.
    fn environment_ready(&mut self, module: &ModuleMetadata) -> Result<StreamingConfig>;

    /// Takes ownership of an issued batch for validation through its batch
    /// methods.
    fn submit_code_batch(&mut self, batch: StreamingBatch<'a>) -> Result<()>;

    /// Waits for and returns an issued batch in any completion order.
    ///
    /// The driver rejects foreign, duplicate, or unfinished batches. To accept
    /// valid input, the scheduler must return each outstanding batch after
    /// successful validation.
    fn poll_code_batch(&mut self) -> Result<StreamingBatch<'a>>;

    /// Reports that all code batches have been submitted.
    fn code_end(&mut self) -> Result<()>;
}

/// The function index and byte extent of a framed code entry.
///
/// Offsets refer to the complete code region. Framing alone does not validate the
/// entry.
#[cfg_attr(not(charon), derive(Debug))]
#[derive(Clone, Copy)]
pub struct StreamingEntry {
    /// The defined-function index, excluding imported functions.
    pub index: usize,
    /// The offset of the entry's size prefix.
    pub start: usize,
    /// The offset of the local declarations, immediately after the size prefix.
    pub contents: usize,
    /// The exclusive end offset of the entry.
    pub end: usize,
}

/// An issued batch of consecutive function entries with private validation state.
///
/// `next_entry` advances only the dispatch cursor. `validate_func` advances the
/// independent validation cursor and stores the first error. The driver accepts a
/// returned batch only when its identity is outstanding and every byte and
/// function has been validated.
pub struct StreamingBatch<'a> {
    /// The module invocation that issued this batch.
    module_id: u64,
    /// The batch's submission index within its invocation.
    batch_id: usize,
    env: Arc<CodeMetadata>,
    /// The consecutive size-prefixed function entries in this batch.
    code: &'a [u8],
    /// The batch's starting offset within the code region.
    code_offset: usize,
    /// The defined-function index of the first entry.
    first_func: usize,
    num_funcs: usize,
    /// The number of entries framed for dispatch.
    num_dispatched: usize,
    dispatch_end: usize,
    /// The number of successfully validated entries.
    num_validated: usize,
    validated_end: usize,
    error: Option<Error>,
}

impl StreamingBatch<'_> {
    /// Declarations shared by all workers validating this module.
    pub fn code_metadata(&self) -> &CodeMetadata {
        &self.env
    }

    /// Returns the number of functions in this batch.
    pub fn len(&self) -> usize {
        self.num_funcs
    }

    /// Returns whether the batch contains no functions.
    pub fn is_empty(&self) -> bool {
        self.num_funcs == 0
    }

    /// Returns whether the batch contains the module's last defined function.
    pub fn is_last(&self) -> bool {
        self.first_func + self.num_funcs == self.env.num_func_defs()
    }

    /// Returns the batch's encoded entries, including size prefixes and local
    /// declarations.
    pub fn code(&self) -> &[u8] {
        self.code
    }

    /// Returns the starting offset of the batch's bytes within the code region.
    pub fn code_offset(&self) -> usize {
        self.code_offset
    }

    /// Frames the next entry and advances the dispatch cursor without validating
    /// it.
    ///
    /// Returns `Error::Host` when no undispatched entries remain.
    pub fn next_entry(&mut self) -> Result<StreamingEntry> {
        if self.num_dispatched >= self.num_funcs {
            return Err(Error::Host);
        }
        let index = self.first_func + self.num_dispatched;
        let entry = frame_entry(self.code, self.dispatch_end, index, self.code_offset)?;
        self.dispatch_end = entry.end - self.code_offset;
        self.num_dispatched += 1;
        Ok(entry)
    }

    /// Validates the next function and reports its context and operators to
    /// `visitor`.
    ///
    /// `index` is the defined-function index, excluding imports, and must match
    /// the next validation entry. Function bounds are relative to
    /// `StreamingBatch::code`; operator cursors are relative to the instruction body.
    /// The first error remains stored and is returned by all later validation
    /// calls.
    pub fn validate_func<V: OpVisitor>(&mut self, index: usize, visitor: &mut V) -> Result<()> {
        if self.error.is_none() {
            match self.validate_next(index, visitor) {
                Ok(end) => {
                    self.num_validated += 1;
                    self.validated_end = end;
                }
                Err(e) => self.error = Some(e),
            }
        }
        match self.error {
            Some(e) => Err(e),
            None => Ok(()),
        }
    }

    /// Validates every remaining entry with accepting operator callbacks.
    fn validate_all(&mut self) {
        let mut ok = true;
        while self.num_validated < self.num_funcs && ok {
            let index = self.first_func + self.num_validated;
            ok = self
                .validate_func(index, &mut crate::DefaultOpVisitor)
                .is_ok();
        }
    }

    fn validate_next<V: OpVisitor>(&self, index: usize, visitor: &mut V) -> Result<usize> {
        if self.num_validated >= self.num_funcs || index != self.first_func + self.num_validated {
            return Err(Error::Host);
        }
        metadata::validate_code_entry_with(self.code, self.validated_end, &self.env, index, visitor)
    }

    fn finish(self) -> Result<()> {
        match self.error {
            Some(e) => Err(e),
            None if self.num_validated == self.num_funcs
                && self.validated_end == self.code.len() =>
            {
                Ok(())
            }
            None => Err(Error::Host),
        }
    }
}

/// Validates one WebAssembly Core 2.0 module using a source and scheduler.
///
/// Batches share ownership of immutable code metadata. Only
/// a successful result certifies a complete module. Soundness requires coherent
/// reads and issued-worker provenance. Completeness also requires returning,
/// accepting callbacks and a scheduler that returns every validated batch.
pub fn validate_streaming<'a, S: StreamingSource, V: StreamingVisitor<'a>>(
    module_id: u64,
    source: &'a S,
    visitor: &mut V,
) -> Result<ModuleMetadata> {
    let bytes = source.environment()?;
    let env_len = add_offset(0, bytes.len())?;
    visitor.custom_region(StreamingRegion::Environment);
    let (prefix, env_end) = metadata::validate_env_with(bytes, visitor)?;
    if env_end != env_len {
        return Err(Error::Host);
    }
    let mut module = prefix.share();
    let code_len = source.code_len();
    let code_end = add_offset(env_len, code_len)?;
    let entries = read_code_header(source, code_len, &module.code)?;
    let config = visitor.environment_ready(&module)?;
    if config.batch_bytes == 0 || config.max_batches == 0 {
        return Err(Error::Host);
    }
    let mut pending = submit_code_batches(
        module_id,
        source,
        &module.code,
        code_len,
        entries,
        &config,
        visitor,
    )?;
    visitor.code_end()?;
    let tail = source.tail()?;
    add_offset(code_end, tail.len())?;
    visitor.custom_region(StreamingRegion::Tail);
    module.data = metadata::validate_tail_with(tail, 0, &module.code, visitor)?;
    retire_all_code_batches(module_id, visitor, &mut pending)?;
    Ok(module)
}

/// Checks the code header against the region size and declared functions,
/// returning the first entry offset.
fn read_code_header<S: StreamingSource>(
    source: &S,
    code_len: usize,
    env: &CodeMetadata,
) -> Result<usize> {
    if code_len == 0 {
        if env.num_func_defs() != 0 {
            return Err(Error::MissingCodeSection);
        }
        return Ok(0);
    }
    let header = read_exact(source, 0, code_len.min(MAX_CODE_HEADER_BYTES))?;
    if header[0] != SECTION_CODE {
        return Err(Error::Host);
    }
    let (len, contents) = read_len(header, 1)?;
    let end = add_offset(contents, len)?;
    if end > code_len {
        return Err(Error::UnexpectedEof);
    }
    if end < code_len {
        return Err(Error::SectionSizeMismatch);
    }
    let (count, entries) = read_len(header, contents)?;
    if entries > end {
        return Err(Error::SectionSizeMismatch);
    }
    if count != env.num_func_defs() {
        return Err(Error::FuncCodeMismatch);
    }
    Ok(entries)
}

/// Acquire one strong reference to the same immutable metadata allocation.
fn share_code(code: &Arc<CodeMetadata>) -> Arc<CodeMetadata> {
    Arc::clone(code)
}

/// Submits every function entry and returns the remaining outstanding batch IDs.
fn submit_code_batches<'a, S: StreamingSource, V: StreamingVisitor<'a>>(
    module_id: u64,
    source: &'a S,
    env: &Arc<CodeMetadata>,
    code_len: usize,
    pos: usize,
    config: &StreamingConfig,
    visitor: &mut V,
) -> Result<Vec<usize>> {
    let mut pending = Vec::new();
    let mut pos = pos;
    let mut func = 0;
    let mut batch_id = 0;
    let num_funcs = env.num_func_defs();
    while func < num_funcs {
        if pending.len() >= config.max_batches {
            retire_code_batch(module_id, visitor, &mut pending)?;
        }
        let (end, next_func) =
            get_next_batch(source, code_len, pos, func, num_funcs, config.batch_bytes)?;
        let bytes = read_exact(source, pos, end)?;
        pending.push(batch_id);
        visitor.submit_code_batch(StreamingBatch {
            module_id,
            batch_id,
            env: share_code(env),
            code: bytes,
            code_offset: pos,
            first_func: func,
            num_funcs: next_func - func,
            num_dispatched: 0,
            dispatch_end: 0,
            num_validated: 0,
            validated_end: 0,
            error: None,
        })?;
        pos = end;
        func = next_func;
        batch_id += 1;
    }
    if pos != code_len {
        return Err(Error::SectionSizeMismatch);
    }
    Ok(pending)
}

/// Frames at least one entry and extends the batch toward its target byte size.
///
/// Workers revalidate framing while validating their entries.
fn get_next_batch<S: StreamingSource>(
    source: &S,
    code_len: usize,
    start: usize,
    first_func: usize,
    num_funcs: usize,
    threshold: usize,
) -> Result<(usize, usize)> {
    let mut pos = start;
    let mut func = first_func;
    let mut batch_bytes = 0;
    let mut done = false;
    while func < num_funcs && !done {
        let prefix = read_exact(source, pos, code_len.min(pos + MAX_LEB_BYTES))?;
        let (len, prefix_len) = read_len(prefix, 0)?;
        if func != first_func && len > threshold - batch_bytes {
            done = true;
        } else {
            let end = add_offset(add_offset(pos, prefix_len)?, len)?;
            if end > code_len {
                return Err(Error::UnexpectedEof);
            }
            batch_bytes += len;
            pos = end;
            func += 1;
            done = batch_bytes >= threshold;
        }
    }
    Ok((pos, func))
}

/// Checks a returned batch's invocation and pending ID, removes that ID, and
/// checks completion.
fn retire_code_batch<'a, V: StreamingVisitor<'a>>(
    module_id: u64,
    visitor: &mut V,
    pending: &mut Vec<usize>,
) -> Result<()> {
    let batch = visitor.poll_code_batch()?;
    if batch.module_id != module_id {
        return Err(Error::Host);
    }
    let mut i = 0;
    while i < pending.len() && pending[i] != batch.batch_id {
        i += 1;
    }
    if i == pending.len() {
        return Err(Error::Host);
    }
    let last = pending.len() - 1;
    pending[i] = pending[last];
    pending.pop();
    batch.finish()
}

/// Retires every outstanding batch, stopping at the first error.
///
/// The separate loop keeps Aeneas's borrowed contexts joinable.
fn retire_all_code_batches<'a, V: StreamingVisitor<'a>>(
    module_id: u64,
    visitor: &mut V,
    pending: &mut Vec<usize>,
) -> Result<()> {
    while !pending.is_empty() {
        retire_code_batch(module_id, visitor, pending)?;
    }
    Ok(())
}

/// Frames an entry and translates its batch-relative offsets into code-region
/// offsets.
fn frame_entry(
    code: &[u8],
    pos: usize,
    index: usize,
    code_offset: usize,
) -> Result<StreamingEntry> {
    let (contents, end) = metadata::code_entry_extent(code, pos)?;
    Ok(StreamingEntry {
        index,
        start: add_offset(code_offset, pos)?,
        contents: add_offset(code_offset, contents)?,
        end: add_offset(code_offset, end)?,
    })
}

/// Reads a `u32` length and returns the next cursor, mapping truncated reads to
/// module EOF errors.
fn read_len(data: &[u8], pos: usize) -> Result<(usize, usize)> {
    match crate::reader::read_u32_leb(data, pos) {
        Ok((value, end)) => Ok((value as usize, end)),
        Err(OpError::UnexpectedEof) => Err(Error::UnexpectedEof),
        Err(error) => Err(Error::Read(error)),
    }
}

fn read_exact<S: StreamingSource>(source: &S, start: usize, end: usize) -> Result<&[u8]> {
    let bytes = source.code(start, end)?;
    if bytes.len() != end - start {
        return Err(Error::UnexpectedEof);
    }
    Ok(bytes)
}

// --- Contiguous validation ---

/// Validates one contiguous module using the shared driver and synchronous
/// worker.
pub(crate) fn validate_module_slice(bytes: &[u8]) -> Result<ModuleMetadata> {
    let (code_start, code_end) = find_code_region(bytes);
    let source = SliceSource {
        env: &bytes[0..code_start],
        code: &bytes[code_start..code_end],
        tail: &bytes[code_end..bytes.len()],
    };
    validate_streaming(0, &source, &mut SyncVisitor { completed: None })
}

/// Locates the code region by framing section headers.
///
/// Malformed or truncated sections remain in a region whose validation reports
/// the error.
fn find_code_region(bytes: &[u8]) -> (usize, usize) {
    let len = bytes.len();
    let mut pos = 8;
    loop {
        if pos >= len {
            return (len, len);
        }
        let id = bytes[pos];
        if id > SECTION_CODE && id != SECTION_DATA_COUNT {
            return (pos, pos);
        }
        let end = match read_len(bytes, pos + 1) {
            Ok((size, contents)) => contents + size.min(len - contents),
            Err(_) => len,
        };
        if id == SECTION_CODE {
            return (pos, end);
        }
        if end == len {
            return (len, len);
        }
        pos = end;
    }
}

/// Immutable slices of a contiguous module's three source regions.
struct SliceSource<'a> {
    env: &'a [u8],
    code: &'a [u8],
    tail: &'a [u8],
}

impl StreamingSource for SliceSource<'_> {
    /// Returns the complete environment region, including the module header.
    fn environment(&self) -> Result<&[u8]> {
        Ok(self.env)
    }

    fn code_len(&self) -> usize {
        self.code.len()
    }

    fn code(&self, start: usize, end: usize) -> Result<&[u8]> {
        if start > end || end > self.code.len() {
            return Err(Error::Host);
        }
        Ok(&self.code[start..end])
    }

    fn tail(&self) -> Result<&[u8]> {
        Ok(self.tail)
    }
}

/// A synchronous worker that validates on submission and holds at most one batch.
///
/// Batches stay within one invocation, so a constant module ID is sufficient.
struct SyncVisitor<'a> {
    completed: Option<StreamingBatch<'a>>,
}
impl metadata::ModuleVisitor for SyncVisitor<'_> {}
impl<'a> StreamingVisitor<'a> for SyncVisitor<'a> {
    fn custom_region(&mut self, _region: StreamingRegion) {}
    fn environment_ready(&mut self, _module: &ModuleMetadata) -> Result<StreamingConfig> {
        Ok(StreamingConfig {
            batch_bytes: 25000,
            max_batches: 1,
        })
    }

    fn submit_code_batch(&mut self, mut batch: StreamingBatch<'a>) -> Result<()> {
        batch.validate_all();
        self.completed = Some(batch);
        Ok(())
    }

    fn poll_code_batch(&mut self) -> Result<StreamingBatch<'a>> {
        match self.completed.take() {
            Some(batch) => Ok(batch),
            None => Err(Error::Host),
        }
    }

    fn code_end(&mut self) -> Result<()> {
        Ok(())
    }
}
