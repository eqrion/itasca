//! Streaming and parallel module validation, verified in Lean.
//!
//! [`validate_streaming`] owns the whole module. It decodes the environment,
//! frames the code section into [`CodeBatch`]es as the bytes arrive, validates
//! the tail at EOF, and accepts only after every batch it issued has come back
//! fully validated. The embedding supplies the module split into three regions
//! through a [`Source`] and schedules function validation through a
//! [`StreamingVisitor`], but neither can replace a phase or certify success:
//! only an `Ok` from [`validate_streaming`] does.
//!
//! The driver checks that the regions are split where [`Source`] says, so an
//! `Ok` means the environment, the code section and the tail, concatenated, are
//! a valid module. A wrong split can only cause a rejection. The embedding
//! still owes:
//!
//! - Successful calls expose coherent views of fixed environment, code and tail
//!   bytes. Rust borrows protect each immutable view; they do not force separate
//!   calls to return matching ranges. The source implementation owes coherence.
//! - `module_id` is unique among invocations whose batches can reach the same
//!   visitor, so a batch from one module cannot be returned to another.
//! - Returned batches come from the corresponding submissions and are advanced
//!   only through their batch operations. The driver checks pending IDs and
//!   successful completion; submission alone does not establish validation.
//! - Callbacks return normally for totality. Acceptance soundness does not
//!   require unexecuted callbacks to return or accept.
//! - The environment and source outlive every worker holding a batch,
//!   including after `validate_streaming` returns an error.

use crate::limits::{add_offset, MAX_CODE_HEADER_BYTES, MAX_LEB_BYTES};
use crate::module::{self, SECTION_CODE};
use crate::{Env, Error, OpError, OpVisitor, Tail, ValidationProfile};
use alloc::vec::Vec;

pub type Result<T> = core::result::Result<T, Error>;

/// Which part of the module a custom section was found in.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub enum Region {
    Environment,
    Tail,
}

/// How the visitor wants the code section divided.
pub struct Config {
    /// Target entry-content bytes, including locals. One entry may exceed it.
    pub batch_bytes: usize,
    /// Most batches submitted and not yet returned by
    /// [`StreamingVisitor::poll_code_batch`].
    pub max_batches: usize,
}

/// One module, split into three regions at its first section whose id is not
/// below the code section's.
///
/// The environment is every byte before that section. The code region is that
/// section if it is the code section, from its id byte to its end, and empty
/// otherwise. The tail is every byte after the code region. A module without
/// such a section is entirely environment. Each region may be a separate
/// allocation.
pub trait Source {
    fn environment(&self) -> Result<&[u8]>;

    /// The code region's length, known before any of it arrives.
    fn code_len(&self) -> usize;

    /// Waits for and returns exactly `start..end` of the code region, where
    /// `start <= end <= code_len()`.
    fn code(&self, start: usize, end: usize) -> Result<&[u8]>;

    /// Waits for EOF and returns the tail.
    fn tail(&self) -> Result<&[u8]>;
}

/// The embedding's side of [`validate_streaming`], called in this order:
///
/// 1. `custom_region(Environment)`, then custom sections before the code.
/// 2. `environment_ready` once, with the decoded environment.
/// 3. `submit_code_batch` for each batch, in module order, interleaved with
///    `poll_code_batch` whenever [`Config::max_batches`] are outstanding.
/// 4. `code_end` once every batch has been submitted.
/// 5. `custom_region(Tail)`, custom sections after the code, then
///    `tail_ready` with the decoded tail.
/// 6. `poll_code_batch` until every outstanding batch has returned.
///
/// Any error stops validation and is the module's result. The visitor may
/// still hold batches at that point and must release them before the
/// environment and source storage they borrow.
pub trait StreamingVisitor<'a>: module::ModuleVisitor {
    /// Later `on_custom_section` offsets are relative to `region`'s bytes.
    fn custom_region(&mut self, region: Region);

    /// The environment is decoded and the code section header checked.
    fn environment_ready(&mut self, env: &Env) -> Result<Config>;

    /// Takes ownership of a batch to validate with
    /// [`CodeBatch::validate_func`].
    fn submit_code_batch(&mut self, batch: CodeBatch<'a>) -> Result<()>;

    /// Blocks until any submitted batch is returned, finished or not.
    fn poll_code_batch(&mut self) -> Result<CodeBatch<'a>>;

    /// Every batch has been submitted.
    fn code_end(&mut self) -> Result<()>;

    fn tail_ready(&mut self, tail: Tail) -> Result<()>;
}

/// One code section entry, as offsets into the code region.
#[cfg_attr(not(charon), derive(Debug))]
#[derive(Clone, Copy)]
pub struct CodeEntry {
    /// The defined function's index, excluding imports.
    pub index: usize,
    /// The entry's size prefix.
    pub start: usize,
    /// The local declarations, just past the size prefix.
    pub contents: usize,
    pub end: usize,
}

/// A run of consecutive code section entries, validated by a worker.
///
/// A batch has two independent cursors. The dispatch cursor, advanced by
/// [`CodeBatch::next_entry`], frames entries for the worker's own use. The
/// validation cursor is advanced only by a successful
/// [`CodeBatch::validate_func`], and the first failure is kept in the batch so
/// a worker cannot drop it. The driver accepts a returned batch only if its
/// validation cursor reached the end and it carries this invocation's
/// identity.
pub struct CodeBatch<'a> {
    /// The invocation that issued this batch.
    module_id: u64,
    /// This batch's position in submission order within that invocation.
    batch_id: usize,
    /// Validation rules fixed by the invocation that issued the batch.
    profile: ValidationProfile,
    env: &'a Env,
    /// The batch's entries, framed back to back.
    code: &'a [u8],
    /// Offset of `code` within the code region.
    code_offset: usize,
    /// Defined-function index of the first entry.
    first_func: usize,
    num_funcs: usize,
    /// Entries framed by `next_entry`, and the offset in `code` after them.
    num_dispatched: usize,
    dispatch_end: usize,
    /// Entries validated, and the offset in `code` after them.
    num_validated: usize,
    validated_end: usize,
    error: Option<Error>,
}

impl CodeBatch<'_> {
    /// The validation rules selected by the issuing invocation.
    pub fn profile(&self) -> ValidationProfile {
        self.profile
    }

    pub fn len(&self) -> usize {
        self.num_funcs
    }

    pub fn is_empty(&self) -> bool {
        self.num_funcs == 0
    }

    /// Whether this batch ends with the module's last function.
    pub fn is_last(&self) -> bool {
        self.first_func + self.num_funcs == self.env.func_type_indices.len()
    }

    /// The batch's entries, beginning at [`CodeBatch::code_offset`].
    pub fn code(&self) -> &[u8] {
        self.code
    }

    /// Offset of [`CodeBatch::code`] within the code region.
    pub fn code_offset(&self) -> usize {
        self.code_offset
    }

    /// Frames the next entry for dispatch. Does not validate anything.
    pub fn next_entry(&mut self) -> Result<CodeEntry> {
        if self.num_dispatched >= self.num_funcs {
            return Err(Error::Host);
        }
        let index = self.first_func + self.num_dispatched;
        let entry = frame_entry(self.code, self.dispatch_end, index, self.code_offset)?;
        self.dispatch_end = entry.end - self.code_offset;
        self.num_dispatched += 1;
        Ok(entry)
    }

    /// Validates the next entry, which must be function `index`, reporting
    /// its operators to `visitor` with positions relative to
    /// [`CodeBatch::code`]. After a failure every call returns the first
    /// error.
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

    fn validate_all(&mut self) {
        let mut ok = true;
        while self.num_validated < self.num_funcs && ok {
            let index = self.first_func + self.num_validated;
            ok = self
                .validate_func(index, &mut crate::EmptyOpVisitor)
                .is_ok();
        }
    }

    fn validate_next<V: OpVisitor>(&self, index: usize, visitor: &mut V) -> Result<usize> {
        if self.num_validated >= self.num_funcs || index != self.first_func + self.num_validated {
            return Err(Error::Host);
        }
        module::validate_code_entry_with(
            self.code,
            self.validated_end,
            self.env,
            index,
            self.profile,
            visitor,
        )
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

/// Validates one module. See the [module documentation](self).
///
/// `profile` selects the rules for environment decoding, every issued batch,
/// and tail decoding. A worker cannot change its batch's profile.
///
/// `env` is output storage, overwritten with the decoded environment. Batches
/// borrow it and the source, so both must outlive the visitor's workers.
///
/// `'data: 'visitor` says that storage outlives the visitor borrow. Aeneas
/// needs the relation in this signature to return the updated visitor and
/// environment when the visitor stores batches.
pub fn validate_streaming<'visitor, 'data: 'visitor, S: Source, V: StreamingVisitor<'data>>(
    module_id: u64,
    profile: ValidationProfile,
    source: &'data S,
    visitor: &'visitor mut V,
    env: &'data mut Env,
) -> Result<()> {
    let bytes = source.environment()?;
    let env_len = add_offset(0, bytes.len())?;
    visitor.custom_region(Region::Environment);
    let (decoded, env_end) = module::validate_env_with(bytes, profile, visitor)?;
    if env_end != env_len {
        return Err(Error::Host);
    }
    *env = decoded;
    validate_remaining(module_id, profile, source, env, env_len, visitor)
}

/// The code section and tail, once `env` is decoded and immutable.
fn validate_remaining<'a, S: Source, V: StreamingVisitor<'a>>(
    module_id: u64,
    profile: ValidationProfile,
    source: &'a S,
    env: &'a Env,
    env_len: usize,
    visitor: &mut V,
) -> Result<()> {
    let code_len = source.code_len();
    let code_end = add_offset(env_len, code_len)?;
    let entries = read_code_header(source, code_len, env)?;
    let config = visitor.environment_ready(env)?;
    if config.batch_bytes == 0 || config.max_batches == 0 {
        return Err(Error::Host);
    }
    let mut pending = submit_code_batches(
        module_id, profile, source, env, code_len, entries, &config, visitor,
    )?;
    visitor.code_end()?;

    let tail_bytes = source.tail()?;
    add_offset(code_end, tail_bytes.len())?;
    visitor.custom_region(Region::Tail);
    let tail = module::validate_tail_with(tail_bytes, 0, env, profile, visitor)?;
    visitor.tail_ready(tail)?;
    retire_all_code_batches(module_id, visitor, &mut pending)
}

/// Checks the code section header against the code region and `env`,
/// returning where its entries begin.
fn read_code_header<S: Source>(source: &S, code_len: usize, env: &Env) -> Result<usize> {
    if code_len == 0 {
        if !env.func_type_indices.is_empty() {
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
    if count != env.func_type_indices.len() {
        return Err(Error::FuncCodeMismatch);
    }
    Ok(entries)
}

/// Submits every entry from `pos` to the end of the code region, returning
/// the IDs of the batches still outstanding.
fn submit_code_batches<'a, S: Source, V: StreamingVisitor<'a>>(
    module_id: u64,
    profile: ValidationProfile,
    source: &'a S,
    env: &'a Env,
    code_len: usize,
    pos: usize,
    config: &Config,
    visitor: &mut V,
) -> Result<Vec<usize>> {
    let mut pending = Vec::new();
    let mut pos = pos;
    let mut func = 0;
    let mut batch_id = 0;
    let num_funcs = env.func_type_indices.len();
    while func < num_funcs {
        if pending.len() >= config.max_batches {
            retire_code_batch(module_id, visitor, &mut pending)?;
        }
        let (end, next_func) =
            get_next_batch(source, code_len, pos, func, num_funcs, config.batch_bytes)?;
        let bytes = read_exact(source, pos, end)?;
        pending.push(batch_id);
        visitor.submit_code_batch(CodeBatch {
            module_id,
            batch_id,
            profile,
            env,
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

/// Frames entries from `start` until their bodies reach `threshold` bytes,
/// returning where the batch ends and the function after its last. Always
/// takes at least one entry. Only locates the batch: the batch revalidates
/// its own framing.
fn get_next_batch<S: Source>(
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

/// Polls one batch, checks that it belongs to this invocation and is
/// outstanding, removes it from `pending`, and returns its result.
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

/// Retires every outstanding batch. A separate function because Aeneas
/// cannot join this loop's contexts inside `validate_remaining`.
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

/// The entry whose size prefix is at `pos` in `code`, which starts at
/// `code_offset` in the code region.
fn frame_entry(code: &[u8], pos: usize, index: usize, code_offset: usize) -> Result<CodeEntry> {
    let (contents, end) = module::code_entry_extent(code, pos)?;
    Ok(CodeEntry {
        index,
        start: add_offset(code_offset, pos)?,
        contents: add_offset(code_offset, contents)?,
        end: add_offset(code_offset, end)?,
    })
}

/// A `u32` length and the position after it. Running out of bytes is
/// [`Error::UnexpectedEof`], since more of the module may never arrive.
fn read_len(data: &[u8], pos: usize) -> Result<(usize, usize)> {
    match crate::reader::read_u32_leb(data, pos) {
        Ok((value, end)) => Ok((value as usize, end)),
        Err(OpError::UnexpectedEof) => Err(Error::UnexpectedEof),
        Err(error) => Err(Error::Read(error)),
    }
}

fn read_exact<S: Source>(source: &S, start: usize, end: usize) -> Result<&[u8]> {
    let bytes = source.code(start, end)?;
    if bytes.len() != end - start {
        return Err(Error::UnexpectedEof);
    }
    Ok(bytes)
}

// --- Contiguous validation ---

/// [`validate_streaming`] over one buffer, validating each batch as it is
/// submitted. This internal adapter implements [`module::validate_module`].
pub(crate) fn validate_module_slice(
    bytes: &[u8],
    profile: ValidationProfile,
) -> Result<module::Module> {
    let (code_start, code_end) = find_code_region(bytes);
    let source = SliceSource {
        env: &bytes[0..code_start],
        code: &bytes[code_start..code_end],
        tail: &bytes[code_end..bytes.len()],
    };
    let mut env = Env::new();
    let mut visitor = SyncVisitor {
        completed: None,
        tail: None,
    };
    validate_streaming(0, profile, &source, &mut visitor, &mut env)?;
    match visitor.tail {
        Some(tail) => Ok(module::Module { env, tail }),
        None => Err(Error::Host),
    }
}

/// Where the [`Source`] code region begins and ends in `bytes`. Only frames
/// section headers, and leaves malformed or truncated sections in a region
/// whose validation reports them.
fn find_code_region(bytes: &[u8]) -> (usize, usize) {
    let len = bytes.len();
    let mut pos = 8;
    loop {
        if pos >= len {
            return (len, len);
        }
        let id = bytes[pos];
        if id > SECTION_CODE {
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

/// A complete module, split into its regions.
struct SliceSource<'a> {
    env: &'a [u8],
    code: &'a [u8],
    tail: &'a [u8],
}

impl Source for SliceSource<'_> {
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

/// Validates each batch on submission and holds at most one, so a constant
/// module ID is enough.
struct SyncVisitor<'a> {
    completed: Option<CodeBatch<'a>>,
    tail: Option<Tail>,
}

impl module::ModuleVisitor for SyncVisitor<'_> {}

impl<'a> StreamingVisitor<'a> for SyncVisitor<'a> {
    fn custom_region(&mut self, _region: Region) {}

    fn environment_ready(&mut self, _env: &Env) -> Result<Config> {
        Ok(Config {
            batch_bytes: 25000,
            max_batches: 1,
        })
    }

    fn submit_code_batch(&mut self, mut batch: CodeBatch<'a>) -> Result<()> {
        batch.validate_all();
        self.completed = Some(batch);
        Ok(())
    }

    fn poll_code_batch(&mut self) -> Result<CodeBatch<'a>> {
        match self.completed.take() {
            Some(batch) => Ok(batch),
            None => Err(Error::Host),
        }
    }

    fn code_end(&mut self) -> Result<()> {
        Ok(())
    }

    fn tail_ready(&mut self, tail: Tail) -> Result<()> {
        self.tail = Some(tail);
        Ok(())
    }
}
