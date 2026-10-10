//! Streaming, parallel module validation. Extracted to Lean, not yet proved.
//!
//! [`validate`] owns the whole module. It decodes the environment, frames the
//! code section into [`Batch`]es as the bytes arrive, validates the tail at
//! EOF, and accepts only after every batch it issued has come back fully
//! validated. The embedding supplies the bytes through a [`Source`] and
//! schedules function validation through a [`Host`], but neither can replace a
//! phase or certify success: only an `Ok` from [`validate`] does.
//!
//! The embedding owes three things the driver cannot check:
//!
//! - Every view a [`Source`] returns is initialized, immutable, and agrees with
//!   every other view of the same bytes.
//! - `module_id` is unique among invocations whose batches can reach the same
//!   [`Host`], so a batch from one module cannot be returned to another.
//! - The environment and source outlive every worker holding a batch,
//!   including after `validate` returns an error.

use crate::limits::{MAX_CODE_HEADER_BYTES, MAX_LEB_BYTES, MAX_MODULE_BYTES};
use crate::module::{self, SECTION_CODE};
use crate::{Env, Error, OpError, OpVisitor, Tail};
use alloc::vec::Vec;

pub type Result<T> = core::result::Result<T, Error>;

/// Which part of the module a custom section was found in.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub enum Region {
    Environment,
    Tail,
}

/// The code section's extent in the module, from its id byte to its end.
#[cfg_attr(not(charon), derive(Debug))]
#[derive(Clone, Copy)]
pub struct CodeRange {
    pub start: usize,
    pub len: usize,
}

/// How the host wants the code section divided.
pub struct Config {
    /// Target body bytes per batch. A single body may exceed it.
    pub batch_bytes: usize,
    /// Most batches submitted and not yet returned by [`Host::complete`].
    pub max_batches: usize,
}

/// The bytes of one module, addressed by absolute module offset.
///
/// A source may hand out separate allocations for each region, but every view
/// it returns must agree with every other view on overlapping bytes.
pub trait Source {
    /// Bytes from offset 0 that include at least every section before the
    /// code section. They may include more: [`SliceSource`] returns the whole
    /// module, and the driver finds the code section itself.
    fn prefix(&self) -> Result<&[u8]>;

    /// Waits for and returns `start..end`. A read of the code section header
    /// may return fewer bytes when the module or the code section ends first.
    /// Every other read must return exactly the requested range.
    fn read(&self, start: usize, end: usize) -> Result<&[u8]>;

    /// Waits for EOF and returns every byte from `start` to the end.
    fn suffix(&self, start: usize) -> Result<&[u8]>;
}

/// A complete module in one contiguous buffer.
pub struct SliceSource<'a> {
    pub bytes: &'a [u8],
}

impl Source for SliceSource<'_> {
    fn prefix(&self) -> Result<&[u8]> {
        Ok(self.bytes)
    }

    fn read(&self, start: usize, end: usize) -> Result<&[u8]> {
        if start > self.bytes.len() || end < start {
            return Err(Error::UnexpectedEof);
        }
        Ok(&self.bytes[start..end.min(self.bytes.len())])
    }

    fn suffix(&self, start: usize) -> Result<&[u8]> {
        if start > self.bytes.len() {
            return Err(Error::UnexpectedEof);
        }
        Ok(&self.bytes[start..])
    }
}

/// Module callbacks, with the region needed to place custom sections.
pub trait Visitor: module::ModuleVisitor {
    /// Called before each region is decoded. Later `on_custom_section` offsets
    /// are relative to `base`, the region's absolute module offset.
    fn custom_region(&mut self, region: Region, base: usize);
}

/// The embedding's side of [`validate`], called in this order:
///
/// 1. `environment_ready` once, with the decoded environment.
/// 2. `submit` for each batch, in module order, interleaved with `complete`
///    whenever [`Config::max_batches`] are outstanding.
/// 3. `code_end` once every batch has been submitted.
/// 4. `tail_ready` with the decoded tail.
/// 5. `complete` until every outstanding batch has returned.
///
/// Any error stops validation and is the module's result. The host may still
/// hold batches at that point and must release them before the environment
/// and source storage they borrow.
pub trait Host<'a>: Visitor {
    /// The environment is decoded and the code section, if any, is located.
    fn environment_ready(&mut self, env: &Env, code: Option<CodeRange>) -> Result<Config>;

    /// Takes ownership of a batch to validate with [`Batch::validate_func`].
    fn submit(&mut self, batch: Batch<'a>) -> Result<()>;

    /// Waits for and returns any submitted batch, finished or not.
    fn complete(&mut self) -> Result<Batch<'a>>;

    /// Every batch has been submitted.
    fn code_end(&mut self) -> Result<()>;

    fn tail_ready(&mut self, tail: Tail) -> Result<()>;
}

/// One code section entry, as offsets relative to the code section's id byte.
#[cfg_attr(not(charon), derive(Debug))]
#[derive(Clone, Copy)]
pub struct Entry {
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
/// [`Batch::next_entry`], frames entries for the worker's own use. The
/// validation cursor is advanced only by a successful
/// [`Batch::validate_func`], and the first failure is kept in the batch so a
/// worker cannot drop it. The driver accepts a returned batch only if its
/// validation cursor reached the end and it carries this invocation's
/// identity.
pub struct Batch<'a> {
    module_id: u64,
    serial: usize,
    env: &'a Env,
    bytes: &'a [u8],
    /// Offset of `bytes` relative to the code section.
    start: usize,
    first_index: usize,
    count: usize,
    dispatched: usize,
    dispatch_pos: usize,
    validated: usize,
    validated_pos: usize,
    error: Option<Error>,
}

impl Batch<'_> {
    pub fn len(&self) -> usize {
        self.count
    }

    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    /// Whether this batch ends with the module's last function.
    pub fn is_last(&self) -> bool {
        self.first_index + self.count == self.env.func_type_indices.len()
    }

    /// The batch's entries, beginning at [`Batch::start`].
    pub fn bytes(&self) -> &[u8] {
        self.bytes
    }

    /// Offset of [`Batch::bytes`] relative to the code section.
    pub fn start(&self) -> usize {
        self.start
    }

    /// Frames the next entry for dispatch. Does not validate anything.
    pub fn next_entry(&mut self) -> Result<Entry> {
        if self.dispatched >= self.count {
            return Err(Error::Host);
        }
        let index = self.first_index + self.dispatched;
        let entry = frame(self.bytes, self.dispatch_pos, index, self.start)?;
        self.dispatch_pos = entry.end - self.start;
        self.dispatched += 1;
        Ok(entry)
    }

    /// Validates the next entry, which must be function `index`, reporting
    /// its operators to `visitor`. After a failure every call returns the
    /// first error.
    pub fn validate_func<V: OpVisitor>(&mut self, index: usize, visitor: &mut V) -> Result<()> {
        if self.error.is_none() {
            match self.validate_next(index, visitor) {
                Ok(end) => {
                    self.validated += 1;
                    self.validated_pos = end;
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
        while self.validated < self.count && ok {
            let index = self.first_index + self.validated;
            ok = self.validate_func(index, &mut crate::EmptyOpVisitor).is_ok();
        }
    }

    fn validate_next<V: OpVisitor>(&self, index: usize, visitor: &mut V) -> Result<usize> {
        if self.validated >= self.count || index != self.first_index + self.validated {
            return Err(Error::Host);
        }
        let entry = frame(self.bytes, self.validated_pos, index, self.start)?;
        let end = entry.end - self.start;
        let bytes = &self.bytes[self.validated_pos..end];
        let validated_end = module::validate_code_entry_with(bytes, 0, self.env, index, visitor)?;
        if validated_end != bytes.len() {
            return Err(Error::SectionSizeMismatch);
        }
        Ok(end)
    }

    fn finish(self) -> Result<()> {
        match self.error {
            Some(e) => Err(e),
            None if self.validated == self.count && self.validated_pos == self.bytes.len() => {
                Ok(())
            }
            None => Err(Error::Host),
        }
    }
}

/// Validates one module. See the [module documentation](self).
///
/// `env` is output storage, overwritten with the decoded environment. Batches
/// borrow it and the source, so both must outlive the host's workers.
///
/// `'data: 'host` says that storage outlives the host borrow. Aeneas needs the
/// relation in this signature to return the updated host and environment when
/// the host stores batches.
pub fn validate<'host, 'data: 'host, S: Source, H: Host<'data>>(
    module_id: u64,
    source: &'data S,
    host: &'host mut H,
    env: &'data mut Env,
) -> Result<()> {
    let prefix = source.prefix()?;
    add_offset(0, prefix.len())?;
    host.custom_region(Region::Environment, 0);
    let (decoded, env_end) = module::validate_env_with(prefix, host)?;
    *env = decoded;
    validate_remaining(module_id, source, env, env_end, host)
}

/// The code section and tail, once `env` is decoded and immutable.
fn validate_remaining<'a, S: Source, H: Host<'a>>(
    module_id: u64,
    source: &'a S,
    env: &'a Env,
    env_end: usize,
    host: &mut H,
) -> Result<()> {
    let (entries, code_end) = read_code_header(source, env_end, env)?;
    let code = CodeRange {
        start: env_end,
        len: code_end - env_end,
    };
    let config = host.environment_ready(env, if code.len == 0 { None } else { Some(code) })?;
    if config.batch_bytes == 0 || config.max_batches == 0 {
        return Err(Error::Host);
    }
    let mut pending = submit_batches(module_id, source, env, &code, entries, &config, host)?;
    host.code_end()?;

    let tail_bytes = source.suffix(code_end)?;
    add_offset(code_end, tail_bytes.len())?;
    host.custom_region(Region::Tail, code_end);
    let tail = module::validate_tail_with(tail_bytes, 0, env, host)?;
    host.tail_ready(tail)?;
    drain(module_id, host, &mut pending)
}

/// Reads the code section header at `start`, returning where its entries
/// begin and where it ends. Both are `start` when there is no code section.
fn read_code_header<S: Source>(source: &S, start: usize, env: &Env) -> Result<(usize, usize)> {
    let header = source.read(start, start + MAX_CODE_HEADER_BYTES)?;
    if header.len() > MAX_CODE_HEADER_BYTES {
        return Err(Error::Host);
    }
    if header.is_empty() || header[0] != SECTION_CODE {
        if !env.func_type_indices.is_empty() {
            return Err(Error::MissingCodeSection);
        }
        return Ok((start, start));
    }
    let (len, contents) = read_len(header, 1)?;
    let relative_end = add_offset(contents, len)?;
    let (count, entries) = read_len(header, contents)?;
    if entries > relative_end {
        return Err(Error::SectionSizeMismatch);
    }
    if count != env.func_type_indices.len() {
        return Err(Error::FuncCodeMismatch);
    }
    Ok((add_offset(start, entries)?, add_offset(start, relative_end)?))
}

/// Submits every entry from `pos` to the end of the code section, returning
/// the serials of the batches still outstanding.
fn submit_batches<'a, S: Source, H: Host<'a>>(
    module_id: u64,
    source: &'a S,
    env: &'a Env,
    code: &CodeRange,
    pos: usize,
    config: &Config,
    host: &mut H,
) -> Result<Vec<usize>> {
    let mut pending = Vec::new();
    let mut pos = pos;
    let mut index = 0;
    let mut serial = 0;
    let count = env.func_type_indices.len();
    let code_end = code.start + code.len;
    while index < count {
        if pending.len() >= config.max_batches {
            collect(module_id, host, &mut pending)?;
        }
        let (end, next_index) = scan_batch(source, code_end, pos, index, count, config.batch_bytes)?;
        let bytes = read_exact(source, pos, end)?;
        pending.push(serial);
        host.submit(Batch {
            module_id,
            serial,
            env,
            bytes,
            start: pos - code.start,
            first_index: index,
            count: next_index - index,
            dispatched: 0,
            dispatch_pos: 0,
            validated: 0,
            validated_pos: 0,
            error: None,
        })?;
        pos = end;
        index = next_index;
        serial += 1;
    }
    if pos != code_end {
        return Err(Error::SectionSizeMismatch);
    }
    Ok(pending)
}

/// Frames entries from `start` until their bodies reach `threshold` bytes,
/// returning the batch's end and the index after its last function. Always
/// takes at least one entry.
fn scan_batch<S: Source>(
    source: &S,
    code_end: usize,
    start: usize,
    first_index: usize,
    count: usize,
    threshold: usize,
) -> Result<(usize, usize)> {
    let mut pos = start;
    let mut index = first_index;
    let mut batch_bytes = 0;
    let mut done = false;
    while index < count && !done {
        let prefix = read_exact(source, pos, code_end.min(pos + MAX_LEB_BYTES))?;
        let (len, prefix_len) = read_len(prefix, 0)?;
        if index != first_index && len > threshold - batch_bytes {
            done = true;
        } else {
            let end = add_offset(add_offset(pos, prefix_len)?, len)?;
            if end > code_end {
                return Err(Error::UnexpectedEof);
            }
            batch_bytes += len;
            pos = end;
            index += 1;
            done = batch_bytes >= threshold;
        }
    }
    Ok((pos, index))
}

/// Takes one returned batch, checks that it belongs to this invocation and is
/// outstanding, and retires it.
fn collect<'a, H: Host<'a>>(module_id: u64, host: &mut H, pending: &mut Vec<usize>) -> Result<()> {
    let batch = host.complete()?;
    if batch.module_id != module_id {
        return Err(Error::Host);
    }
    let mut i = 0;
    while i < pending.len() && pending[i] != batch.serial {
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

/// Collects every outstanding batch. A separate function because Aeneas
/// cannot join this loop's contexts inside `validate_remaining`.
fn drain<'a, H: Host<'a>>(module_id: u64, host: &mut H, pending: &mut Vec<usize>) -> Result<()> {
    while !pending.is_empty() {
        collect(module_id, host, pending)?;
    }
    Ok(())
}

/// The entry at `pos` in `bytes`, which start at code section offset `base`.
fn frame(bytes: &[u8], pos: usize, index: usize, base: usize) -> Result<Entry> {
    let (contents, end) = module::code_entry_extent(bytes, pos)?;
    Ok(Entry {
        index,
        start: add_offset(base, pos)?,
        contents: add_offset(base, contents)?,
        end: add_offset(base, end)?,
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

/// `a + b`, rejecting any offset beyond the largest module.
fn add_offset(a: usize, b: usize) -> Result<usize> {
    if a > MAX_MODULE_BYTES || b > MAX_MODULE_BYTES - a {
        return Err(Error::ModuleTooLarge);
    }
    Ok(a + b)
}

fn read_exact<S: Source>(source: &S, start: usize, end: usize) -> Result<&[u8]> {
    let bytes = source.read(start, end)?;
    if bytes.len() != end - start {
        return Err(Error::UnexpectedEof);
    }
    Ok(bytes)
}

// --- Contiguous validation ---

/// [`validate`] over one buffer, validating each batch as it is submitted.
pub(crate) fn validate_slice(bytes: &[u8]) -> Result<module::Module> {
    let source = SliceSource { bytes };
    let mut env = Env::new();
    let mut host = InlineHost {
        completed: None,
        tail: None,
    };
    validate(0, &source, &mut host, &mut env)?;
    match host.tail {
        Some(tail) => Ok(module::Module { env, tail }),
        None => Err(Error::Host),
    }
}

/// Holds at most one batch, so a constant module ID is enough.
struct InlineHost<'a> {
    completed: Option<Batch<'a>>,
    tail: Option<Tail>,
}

impl module::ModuleVisitor for InlineHost<'_> {}

impl Visitor for InlineHost<'_> {
    fn custom_region(&mut self, _region: Region, _base: usize) {}
}

impl<'a> Host<'a> for InlineHost<'a> {
    fn environment_ready(&mut self, _env: &Env, _code: Option<CodeRange>) -> Result<Config> {
        Ok(Config {
            batch_bytes: 25000,
            max_batches: 1,
        })
    }

    fn submit(&mut self, mut batch: Batch<'a>) -> Result<()> {
        batch.validate_all();
        self.completed = Some(batch);
        Ok(())
    }

    fn complete(&mut self) -> Result<Batch<'a>> {
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
