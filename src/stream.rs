//! Single-entry streaming validation experiment. Not yet formally verified.
//! The driver owns phase order and completion accounting. The embedding supplies
//! immutable byte ranges and a scheduler for parallel function validation.
use crate::limits::MAX_MODULE_BYTES;
use crate::{module, reader, Env, Error, OpError, OpVisitor, Tail};
use alloc::vec::Vec;

pub type Result<T> = core::result::Result<T, Error>;

#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub enum Region {
    Environment,
    Tail,
}

#[cfg_attr(not(charon), derive(Debug))]
#[derive(Clone, Copy)]
pub struct CodeRange {
    pub start: usize,
    pub len: usize,
}

pub struct Config {
    /// Target body bytes per batch; a single large body may exceed this.
    pub batch_bytes: usize,
    /// Maximum submitted batches whose completion has not been consumed.
    pub max_batches: usize,
}

/// Immutable views of one logical module. All views must agree on overlapping
/// bytes. `prefix` includes every section before code, and may include more.
/// `read` waits for the requested bytes, but may stop at EOF or the end of the
/// code allocation when reading its header. Exact body ranges must be contiguous.
/// `suffix` waits for EOF and returns all bytes starting at the given offset.
pub trait Source {
    fn prefix(&self) -> Result<&[u8]>;
    fn read(&self, start: usize, end: usize) -> Result<&[u8]>;
    fn suffix(&self, start: usize) -> Result<&[u8]>;
}

/// A complete module needs no section scan or copies to serve the driver.
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

pub trait Visitor: module::ModuleVisitor {
    /// Selects the region for subsequent `on_custom_section` offsets.
    fn custom_region(&mut self, region: Region, base: usize);
}

/// Submit transfers a batch to the host; complete returns any finished batch.
/// The driver consumes every issued batch before acceptance. Batches borrow the
/// caller's environment storage and source, which must outlive all workers.
pub trait Host<'a>: Visitor {
    fn environment_ready(&mut self, env: &Env, code: Option<CodeRange>) -> Result<Config>;
    fn submit(&mut self, batch: Batch<'a>) -> Result<()>;
    fn complete(&mut self) -> Result<Batch<'a>>;
    fn code_end(&mut self) -> Result<()>;
    fn tail_ready(&mut self, tail: Tail) -> Result<()>;
}

#[cfg_attr(not(charon), derive(Debug))]
#[derive(Clone, Copy)]
/// Entry offsets are relative to the code region, including its section header.
pub struct Entry {
    pub index: usize,
    pub start: usize,
    pub contents: usize,
    pub end: usize,
}

/// A move-only batch backed by one immutable range. Dispatch and validation
/// have independent cursors; only `validate_func` advances validation. The
/// private module and batch IDs bind a completion to its submission.
pub struct Batch<'a> {
    module_id: u64,
    serial: usize,
    env: &'a Env,
    bytes: &'a [u8],
    start: usize,
    first_index: usize,
    count: usize,
    dispatch_index: usize,
    dispatch_pos: usize,
    next: usize,
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
    pub fn is_last(&self) -> bool {
        self.first_index + self.count == self.env.func_type_indices.len()
    }
    pub fn bytes(&self) -> &[u8] {
        self.bytes
    }
    pub fn start(&self) -> usize {
        self.start
    }

    pub fn next_entry(&mut self) -> Result<Entry> {
        if self.dispatch_index >= self.count {
            return Err(Error::FuncCodeMismatch);
        }
        let entry = frame(
            self.bytes,
            self.dispatch_pos,
            self.first_index + self.dispatch_index,
            self.start,
        )?;
        self.dispatch_pos = entry.end - self.start;
        self.dispatch_index += 1;
        Ok(entry)
    }

    /// A failure remains in the token even if the worker ignores it. The
    /// expected function index prevents repeated calls certifying another body.
    pub fn validate_func<V: OpVisitor>(
        &mut self,
        index: usize,
        visitor: &mut V,
    ) -> core::result::Result<(), &Error> {
        if let Some(ref error) = self.error {
            return Err(error);
        }
        let result = self.validate_next(index, visitor);
        match result {
            Ok(end) => {
                self.next += 1;
                self.validated_pos = end;
                Ok(())
            }
            Err(e) => {
                self.error = Some(e);
                match &self.error {
                    Some(error) => Err(error),
                    None => unreachable!(),
                }
            }
        }
    }

    fn validate_next<V: OpVisitor>(&self, index: usize, visitor: &mut V) -> Result<usize> {
        if self.next >= self.count || index != self.first_index + self.next {
            return Err(Error::FuncCodeMismatch);
        }
        let data = self.bytes;
        let entry = frame(data, self.validated_pos, index, self.start)?;
        let end = entry.end - self.start;
        let bytes = &data[self.validated_pos..end];
        let validated_end = module::validate_code_entry_with(bytes, 0, self.env, index, visitor)?;
        if validated_end != bytes.len() {
            return Err(Error::SectionSizeMismatch);
        }
        Ok(end)
    }

    fn finish(self) -> Result<()> {
        match self.error {
            Some(e) => Err(e),
            None if self.next == self.count && self.validated_pos == self.bytes.len() => Ok(()),
            None => Err(Error::FuncCodeMismatch),
        }
    }
}

fn frame(data: &[u8], pos: usize, index: usize, base: usize) -> Result<Entry> {
    let (len, contents) = u32_leb(data, pos)?;
    let end = size(contents, len)?;
    if end > data.len() {
        return Err(Error::UnexpectedEof);
    }
    Ok(Entry {
        index,
        start: size(base, pos)?,
        contents: size(base, contents)?,
        end: size(base, end)?,
    })
}

fn u32_leb(data: &[u8], pos: usize) -> Result<(usize, usize)> {
    match reader::read_u32_leb(data, pos) {
        Ok((value, end)) => Ok((value as usize, end)),
        Err(OpError::UnexpectedEof) => Err(Error::UnexpectedEof),
        Err(error) => Err(Error::Read(error)),
    }
}

fn size(a: usize, b: usize) -> Result<usize> {
    if a > MAX_MODULE_BYTES || b > MAX_MODULE_BYTES - a {
        return Err(Error::ModuleTooLarge);
    }
    Ok(a + b)
}

fn range<S: Source>(source: &S, start: usize, end: usize) -> Result<&[u8]> {
    let bytes = source.read(start, end)?;
    if bytes.len() != end - start {
        return Err(Error::UnexpectedEof);
    }
    Ok(bytes)
}

fn collect<'a, H: Host<'a>>(module_id: u64, host: &mut H, pending: &mut Vec<usize>) -> Result<()> {
    let batch = host.complete()?;
    if batch.module_id != module_id {
        return Err(Error::FuncCodeMismatch);
    }
    let i = find_pending(pending, batch.serial)?;
    let last = pending.len() - 1;
    pending[i] = pending[last];
    pending.pop();
    batch.finish()
}

/// Validate one logical module, discovering section boundaries in the driver.
/// Success includes consumption of every successfully validated batch.
///
/// `module_id` must be unique among invocations whose batches can reach the same
/// host. The embedding allocates IDs; the driver checks them on completion.
/// `env` is output storage, overwritten by environment decoding. Only an `Ok`
/// result certifies module acceptance. On error the host may still own jobs;
/// release them before reusing the environment or source storage.
pub fn validate<'host, 'data: 'host, S: Source, H: Host<'data>>(
    module_id: u64,
    source: &'data S,
    host: &'host mut H,
    env: &'data mut Env,
) -> Result<()> {
    let data = source.prefix()?;
    size(0, data.len())?;
    host.custom_region(Region::Environment, 0);
    let (decoded, env_end) = module::validate_env_with(data, host)?;
    *env = decoded;
    validate_remaining(module_id, source, env, env_end, host)
}

fn code_start<S: Source>(source: &S, start: usize, env: &Env) -> Result<(usize, usize)> {
    let header = source.read(start, start + 11)?;
    if header.len() > 11 {
        return Err(Error::SectionSizeMismatch);
    }
    if header.is_empty() || header[0] != 10 {
        if !env.func_type_indices.is_empty() {
            return Err(Error::MissingCodeSection);
        }
        return Ok((start, start));
    }
    let (len, contents) = u32_leb(header, 1)?;
    let relative_end = size(contents, len)?;
    let end = size(start, relative_end)?;
    let (count, entries) = u32_leb(header, contents)?;
    if entries > relative_end {
        return Err(Error::SectionSizeMismatch);
    }
    if count != env.func_type_indices.len() {
        return Err(Error::FuncCodeMismatch);
    }
    Ok((size(start, entries)?, end))
}

fn validate_remaining<'a, S: Source, H: Host<'a>>(
    module_id: u64,
    source: &'a S,
    env: &'a Env,
    env_end: usize,
    host: &mut H,
) -> Result<()> {
    let (entries, code_end) = code_start(source, env_end, env)?;
    let code = CodeRange {
        start: env_end,
        len: code_end - env_end,
    };
    let config = host.environment_ready(env, if code.len == 0 { None } else { Some(code) })?;
    if config.batch_bytes == 0 || config.max_batches == 0 {
        return Err(Error::FuncCodeMismatch);
    }
    let mut pending = dispatch(module_id, source, env, &code, entries, &config, host)?;
    host.code_end()?;
    let tail_bytes = source.suffix(code_end)?;
    size(code_end, tail_bytes.len())?;
    host.custom_region(Region::Tail, code_end);
    let tail = module::validate_tail_with(tail_bytes, 0, env, host)?;
    host.tail_ready(tail)?;
    drain(module_id, host, &mut pending)
}

fn dispatch<'a, S: Source, H: Host<'a>>(
    module_id: u64,
    source: &'a S,
    env: &'a Env,
    code: &CodeRange,
    start: usize,
    config: &Config,
    host: &mut H,
) -> Result<Vec<usize>> {
    let mut pending = Vec::new();
    let mut pos = start;
    let mut index = 0;
    let mut serial = 0;
    let code_end = code.start + code.len;
    while index < env.func_type_indices.len() {
        if pending.len() >= config.max_batches {
            collect(module_id, host, &mut pending)?;
        }
        let (end, next_index) = scan_batch(
            source,
            code_end,
            pos,
            index,
            env.func_type_indices.len(),
            config.batch_bytes,
        )?;
        let bytes = range(source, pos, end)?;
        pending.push(serial);
        host.submit(Batch {
            module_id,
            serial,
            env,
            bytes,
            start: pos - code.start,
            first_index: index,
            count: next_index - index,
            dispatch_index: 0,
            dispatch_pos: 0,
            next: 0,
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

fn find_pending(pending: &[usize], serial: usize) -> Result<usize> {
    let mut i = 0;
    while i < pending.len() {
        if pending[i] == serial {
            return Ok(i);
        }
        i += 1;
    }
    Err(Error::FuncCodeMismatch)
}
fn drain<'a, H: Host<'a>>(module_id: u64, host: &mut H, pending: &mut Vec<usize>) -> Result<()> {
    while !pending.is_empty() {
        collect(module_id, host, pending)?;
    }
    Ok(())
}

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
        let prefix = range(source, pos, code_end.min(pos + 5))?;
        let (len, prefix_len) = u32_leb(prefix, 0)?;
        if index != first_index && len > threshold - batch_bytes {
            done = true;
        } else {
            let contents = size(pos, prefix_len)?;
            let end = size(contents, len)?;
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

/// Synchronous adapter for the same module driver used by streaming consumers.
pub(crate) fn validate_slice(bytes: &[u8]) -> Result<module::Module> {
    let source = SliceSource { bytes };
    let mut env = Env::new();
    let tail;
    {
        let mut host = InlineHost {
            completed: None,
            tail: None,
        };
        validate(0, &source, &mut host, &mut env)?;
        tail = match host.tail.take() {
            Some(tail) => tail,
            None => return Err(Error::SectionSizeMismatch),
        };
    }
    Ok(module::Module { env, tail })
}

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
            None => Err(Error::FuncCodeMismatch),
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

impl Batch<'_> {
    fn validate_all(&mut self) {
        let mut failed = false;
        while self.next < self.count && !failed {
            let index = self.first_index + self.next;
            failed = match self.validate_func(index, &mut crate::EmptyOpVisitor) {
                Ok(()) => false,
                Err(_) => true,
            };
        }
    }
}
