#![cfg(feature = "stream")]

use itasca::stream::{self, Batch, CodeRange, Config, Host, Region, Result, Source, Visitor};
use itasca::{module, CustomSection, EmptyOpVisitor, Env, Error, OpError, Tail, VisitError};
use std::cell::Cell;
use std::thread::{Scope, ScopedJoinHandle};

// --- A module split into three allocations, as a streaming embedding sees it ---

#[derive(Default)]
struct SplitSource {
    env: Vec<u8>,
    code: Vec<u8>,
    tail: Vec<u8>,
    /// Code section bytes past this offset never arrive.
    early_eof: Option<usize>,
    tail_seen: Cell<bool>,
}

impl SplitSource {
    /// Splits at the code section, which may be truncated. A module whose
    /// environment does not validate stays in `env`.
    fn new(bytes: &[u8]) -> Self {
        let (start, end) = code_section_extent(bytes).unwrap_or((bytes.len(), bytes.len()));
        SplitSource {
            env: bytes[..start].to_vec(),
            code: bytes[start..end].to_vec(),
            tail: bytes[end..].to_vec(),
            ..Default::default()
        }
    }
}

fn code_section_extent(bytes: &[u8]) -> Option<(usize, usize)> {
    let (_, start) = module::validate_env(bytes).ok()?;
    if bytes.get(start) != Some(&10) {
        return None;
    }
    let mut pos = start + 1;
    let mut len = 0;
    let mut shift = 1;
    loop {
        let byte = *bytes.get(pos)?;
        pos += 1;
        len += usize::from(byte % 128) * shift;
        if byte < 128 {
            return Some((start, (pos + len).min(bytes.len())));
        }
        shift *= 128;
    }
}

impl Source for SplitSource {
    fn prefix(&self) -> Result<&[u8]> {
        Ok(&self.env)
    }

    fn read(&self, start: usize, end: usize) -> Result<&[u8]> {
        if self.code.is_empty() {
            return self
                .env
                .get(start..end.min(self.env.len()))
                .ok_or(Error::UnexpectedEof);
        }
        let start = start
            .checked_sub(self.env.len())
            .ok_or(Error::UnexpectedEof)?;
        let end = (end - self.env.len()).min(self.code.len());
        if self.early_eof.is_some_and(|n| end > n) {
            return Err(Error::UnexpectedEof);
        }
        self.code.get(start..end).ok_or(Error::UnexpectedEof)
    }

    fn suffix(&self, start: usize) -> Result<&[u8]> {
        self.tail_seen.set(true);
        if self.code.is_empty() {
            if !self.tail.is_empty() {
                return Err(Error::SectionSizeMismatch);
            }
            return self.env.get(start..).ok_or(Error::UnexpectedEof);
        }
        let expected = self.env.len() + self.code.len();
        if start > expected {
            return Err(Error::UnexpectedEof);
        }
        if start != expected {
            return Err(Error::SectionSizeMismatch);
        }
        Ok(&self.tail)
    }
}

// --- A host that records what it saw, and how to misbehave ---

#[derive(Default)]
struct TestHost {
    source: SplitSource,
    parallel: bool,
    /// Return batches without validating them.
    skip: bool,
    /// Validate each function twice.
    repeat: bool,
    fail_complete: bool,
    peak: usize,
    submitted: usize,
    completed: usize,
    custom_base: usize,
    custom_offsets: Vec<(usize, usize)>,
    decoded_tail: Option<Tail>,
}

impl TestHost {
    fn new(bytes: &[u8]) -> Self {
        TestHost {
            source: SplitSource::new(bytes),
            ..Default::default()
        }
    }

    fn validate(&mut self) -> Result<Env> {
        let source = std::mem::take(&mut self.source);
        let mut env = Env::new();
        let result = std::thread::scope(|threads| {
            stream::validate(1, &source, &mut TestScheduler::new(self, threads), &mut env)
        });
        self.source = source;
        result.map(|()| env)
    }
}

impl module::ModuleVisitor for TestHost {
    fn on_custom_section(&mut self, s: CustomSection) -> core::result::Result<(), VisitError> {
        self.custom_offsets.push((
            self.custom_base + s.payload_start,
            self.custom_base + s.payload_end,
        ));
        Ok(())
    }
}

impl module::CodeVisitor for TestHost {}

impl Visitor for TestHost {
    fn custom_region(&mut self, _: Region, base: usize) {
        self.custom_base = base;
    }
}

/// Runs batches inline or on scoped threads, completing the newest first.
struct TestScheduler<'h, 'jobs, 'env> {
    host: &'h mut TestHost,
    threads: &'jobs Scope<'jobs, 'env>,
    pending: Vec<Batch<'env>>,
    workers: Vec<ScopedJoinHandle<'jobs, Batch<'env>>>,
    /// Returned by the next `complete` instead of any submitted batch.
    foreign: Option<Batch<'env>>,
}

impl<'h, 'jobs, 'env> TestScheduler<'h, 'jobs, 'env> {
    fn new(host: &'h mut TestHost, threads: &'jobs Scope<'jobs, 'env>) -> Self {
        TestScheduler {
            host,
            threads,
            pending: Vec::new(),
            workers: Vec::new(),
            foreign: None,
        }
    }
}

impl module::ModuleVisitor for TestScheduler<'_, '_, '_> {
    fn on_custom_section(&mut self, s: CustomSection) -> core::result::Result<(), VisitError> {
        self.host.on_custom_section(s)
    }
}

impl Visitor for TestScheduler<'_, '_, '_> {
    fn custom_region(&mut self, region: Region, base: usize) {
        self.host.custom_region(region, base);
    }
}

impl<'a> Host<'a> for TestScheduler<'_, '_, 'a> {
    fn environment_ready(&mut self, _: &Env, _: Option<CodeRange>) -> Result<Config> {
        Ok(Config {
            batch_bytes: 4,
            max_batches: 2,
        })
    }

    fn submit(&mut self, mut batch: Batch<'a>) -> Result<()> {
        let skip = self.host.skip;
        let repeat = self.host.repeat;
        let validate = move || {
            if !skip {
                for _ in 0..batch.len() {
                    let index = batch.next_entry().unwrap().index;
                    if batch.validate_func(index, &mut EmptyOpVisitor).is_err() {
                        break;
                    }
                    if repeat {
                        let _ = batch.validate_func(index, &mut EmptyOpVisitor);
                    }
                }
            }
            batch
        };
        if self.host.parallel {
            self.workers.push(self.threads.spawn(validate));
        } else {
            self.pending.push(validate());
        }
        self.host.submitted += 1;
        self.host.peak = self.host.peak.max(self.pending.len() + self.workers.len());
        Ok(())
    }

    fn complete(&mut self) -> Result<Batch<'a>> {
        if self.host.fail_complete {
            return Err(Error::Host);
        }
        self.host.completed += 1;
        if let Some(batch) = self.foreign.take() {
            return Ok(batch);
        }
        if self.host.parallel {
            return Ok(self.workers.pop().unwrap().join().unwrap());
        }
        self.pending.pop().ok_or(Error::Host)
    }

    fn code_end(&mut self) -> Result<()> {
        Ok(())
    }

    fn tail_ready(&mut self, tail: Tail) -> Result<()> {
        self.host.decoded_tail = Some(tail);
        Ok(())
    }
}

/// The existing whole-module orchestration, kept as an independent oracle.
struct LegacyVisitor;
impl module::ModuleVisitor for LegacyVisitor {}
impl module::CodeVisitor for LegacyVisitor {}

/// `n` functions of type `[] -> []`, each with the single instruction `op`.
fn functions(n: u8, op: u8) -> Vec<u8> {
    let mut bytes = b"\0asm\x01\0\0\0\x01\x04\x01\x60\0\0".to_vec();
    bytes.extend([3, n + 1, n]);
    bytes.extend(vec![0; n as usize]);
    bytes.extend([10, 1 + n * 4, n]);
    for _ in 0..n {
        bytes.extend([3, 0, op, 0x0b]);
    }
    bytes
}

// --- Tests ---

#[test]
fn corpus_agrees_with_existing_validator() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/spec");
    let mut checked = 0;
    for kind in ["valid", "invalid", "malformed"] {
        let Ok(files) = std::fs::read_dir(root.join(kind)) else {
            continue;
        };
        for file in files {
            let path = file.unwrap().path();
            if path.extension().is_none_or(|e| e != "wasm") {
                continue;
            }
            let bytes = std::fs::read(&path).unwrap();
            let expected = module::validate_module_with(&bytes, &mut LegacyVisitor);

            let contiguous = module::validate_module(&bytes);
            assert_eq!(
                contiguous.is_ok(),
                expected.is_ok(),
                "slice {}: {contiguous:?} vs {expected:?}",
                path.display()
            );
            if let (Ok(actual), Ok(expected)) = (&contiguous, &expected) {
                assert_eq!(actual, expected);
            }

            let mut host = TestHost::new(&bytes);
            let split = host.validate();
            assert_eq!(
                split.is_ok(),
                expected.is_ok(),
                "split {}: {split:?} vs {expected:?}",
                path.display()
            );
            if let (Ok(actual), Ok(expected)) = (split, expected) {
                assert_eq!(actual, expected.env);
                assert_eq!(host.decoded_tail.take().unwrap(), expected.tail);
            }
            checked += 1;
        }
    }
    assert!(checked > 1000);
}

#[test]
fn bounded_out_of_order_completion() {
    let mut host = TestHost::new(&functions(20, 1));
    host.validate().unwrap();
    assert_eq!(host.peak, 2);
    assert_eq!(host.completed, host.submitted);
    assert!(host.source.tail_seen.get());
}

#[test]
fn parallel_batches_are_consumed_before_acceptance() {
    let mut host = TestHost::new(&functions(20, 1));
    host.parallel = true;
    host.validate().unwrap();
    assert_eq!(host.completed, host.submitted);
    assert_eq!(host.peak, 2);
}

#[test]
fn ignored_worker_failure_remains_in_batch() {
    let mut host = TestHost::new(&functions(1, 0xff));
    assert_eq!(
        host.validate().unwrap_err(),
        Error::Body(OpError::UnrecognizedOpcode)
    );
    assert!(host.source.tail_seen.get());
}

#[test]
fn missing_and_repeated_validation_reject() {
    let mut host = TestHost::new(&functions(2, 1));
    host.skip = true;
    assert_eq!(host.validate().unwrap_err(), Error::Host);
    let mut host = TestHost::new(&functions(2, 1));
    host.repeat = true;
    assert_eq!(host.validate().unwrap_err(), Error::Host);
}

#[test]
fn completion_from_another_module_rejects() {
    let good = SplitSource::new(&functions(1, 1));
    let bad = SplitSource::new(&functions(1, 0xff));
    let mut good_env = Env::new();
    let mut bad_env = Env::new();
    let mut host = TestHost {
        fail_complete: true,
        ..Default::default()
    };
    std::thread::scope(|threads| {
        let mut scheduler = TestScheduler::new(&mut host, threads);
        // Keep a genuinely validated batch from an earlier invocation.
        assert!(stream::validate(1, &good, &mut scheduler, &mut good_env).is_err());
        scheduler.foreign = scheduler.pending.pop();
        assert!(scheduler.foreign.is_some());
        scheduler.host.fail_complete = false;
        // Both batches have serial zero and the same function and byte ranges,
        // so only the module ID tells them apart.
        assert_eq!(
            stream::validate(2, &bad, &mut scheduler, &mut bad_env),
            Err(Error::Host)
        );
    });
}

#[test]
fn every_truncated_arrival_rejects() {
    let bytes = functions(5, 1);
    let len = SplitSource::new(&bytes).code.len();
    for end in 0..len {
        let mut host = TestHost::new(&bytes);
        host.source.early_eof = Some(end);
        assert!(host.validate().is_err(), "end={end}");
    }
}

#[test]
fn truncated_code_allocation_reports_eof() {
    let mut host = TestHost::new(&functions(1, 1));
    host.source.code.pop();
    assert_eq!(host.validate().unwrap_err(), Error::UnexpectedEof);
}

#[test]
fn section_boundaries_and_tail_are_checked() {
    let bytes = functions(1, 1);
    let mut host = TestHost::new(&bytes);
    host.source.code.push(0);
    assert_eq!(host.validate().unwrap_err(), Error::SectionSizeMismatch);
    let mut host = TestHost::new(&bytes);
    host.source.tail = vec![1, 0];
    assert_eq!(host.validate().unwrap_err(), Error::SectionOutOfOrder);
    assert_eq!(host.submitted, 1);
}

#[test]
fn caller_joins_workers_when_tail_or_input_rejects() {
    let bytes = functions(20, 1);
    let mut host = TestHost::new(&bytes);
    host.parallel = true;
    host.source.tail = vec![0xff];
    assert!(host.validate().is_err());
    assert!(host.submitted > host.completed);
    // The scoped workers have all joined, so the same host can validate again.
    host.source.tail.clear();
    assert!(host.validate().is_ok());

    let mut host = TestHost::new(&bytes);
    host.parallel = true;
    host.source.early_eof = Some(15);
    assert!(host.validate().is_err());
    assert!(host.submitted > 0);
    host.source.early_eof = None;
    assert!(host.validate().is_ok());
}

/// Modules with no code section, an empty one, and two functions, each with a
/// custom section before and after the code section.
fn modules_with_custom_sections() -> Vec<Vec<u8>> {
    let custom = [0, 4, 1, b'x', b'y', b'z'];
    let no_code = b"\0asm\x01\0\0\0\x05\x03\x01\0\x01\x0b\x06\x01\0\x41\0\x0b\0";
    let empty_code = b"\0asm\x01\0\0\0\x0a\x82\0\x80\0";
    let mut modules = vec![no_code.to_vec(), empty_code.to_vec(), functions(2, 1)];
    for bytes in &mut modules {
        bytes.splice(8..8, custom);
        bytes.extend(custom);
    }
    modules
}

#[test]
fn custom_section_offsets_are_absolute() {
    for bytes in modules_with_custom_sections() {
        let mut expected = TestHost::default();
        let decoded = module::validate_module_with(&bytes, &mut expected).unwrap();
        assert_eq!(expected.custom_offsets.len(), 2);

        let mut split = TestHost::new(&bytes);
        assert_eq!(split.validate().unwrap(), decoded.env);
        assert_eq!(split.custom_offsets, expected.custom_offsets);

        let mut sliced = TestHost::default();
        let source = stream::SliceSource { bytes: &bytes };
        let mut env = Env::new();
        std::thread::scope(|threads| {
            let mut scheduler = TestScheduler::new(&mut sliced, threads);
            stream::validate(1, &source, &mut scheduler, &mut env).unwrap();
        });
        assert_eq!(env, decoded.env);
        assert_eq!(sliced.decoded_tail.unwrap(), decoded.tail);
        assert_eq!(sliced.custom_offsets, expected.custom_offsets);
    }
}

#[test]
fn every_truncated_slice_agrees_with_existing_validator() {
    for bytes in modules_with_custom_sections() {
        for end in 0..bytes.len() {
            let prefix = &bytes[..end];
            assert_eq!(
                module::validate_module(prefix).is_ok(),
                module::validate_module_with(prefix, &mut LegacyVisitor).is_ok(),
                "truncated at {end}: {prefix:?}",
            );
        }
    }
}
