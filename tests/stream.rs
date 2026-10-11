use itasca::signature::{BlockType, ResultType, TypePart};
use itasca::stream::{self, CodeBatch, Config, Region, Result, Source, StreamingVisitor};
use itasca::{
    module, CustomSection, EmptyOpVisitor, Env, Error, OpError, Tail, ValidationProfile, VisitError,
};
use std::cell::{Cell, RefCell};
use std::sync::{Arc, Mutex};
use std::thread::{Scope, ScopedJoinHandle};
use wasmparser::{Validator, WasmFeatures};

// --- A module split into three allocations, as a streaming embedding sees it ---

#[derive(Default)]
struct SplitSource {
    env: Vec<u8>,
    code: Vec<u8>,
    tail: Vec<u8>,
    /// Code section bytes past this offset never arrive.
    early_eof: Option<usize>,
    tail_seen: Cell<bool>,
    reads: RefCell<Vec<(usize, usize)>>,
}

impl SplitSource {
    /// Splits at the first section whose id is not below the code section's,
    /// clamping a truncated code section. A module whose environment does not
    /// validate stays in `env`.
    fn new(bytes: &[u8]) -> Self {
        Self::with_profile(bytes, ValidationProfile::Wasm1)
    }

    fn with_profile(bytes: &[u8], profile: ValidationProfile) -> Self {
        let (start, end) = code_region(bytes, profile).unwrap_or((bytes.len(), bytes.len()));
        SplitSource {
            env: bytes[..start].to_vec(),
            code: bytes[start..end].to_vec(),
            tail: bytes[end..].to_vec(),
            ..Default::default()
        }
    }
}

fn code_region(bytes: &[u8], profile: ValidationProfile) -> Option<(usize, usize)> {
    let (_, start) = module::validate_env(bytes, profile).ok()?;
    if bytes.get(start) != Some(&10) {
        return Some((start, start));
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
    fn environment(&self) -> Result<&[u8]> {
        Ok(&self.env)
    }

    fn code_len(&self) -> usize {
        self.code.len()
    }

    fn code(&self, start: usize, end: usize) -> Result<&[u8]> {
        assert!(start <= end && end <= self.code.len());
        self.reads.borrow_mut().push((start, end));
        if self.early_eof.is_some_and(|n| end > n) {
            return Err(Error::UnexpectedEof);
        }
        Ok(&self.code[start..end])
    }

    fn tail(&self) -> Result<&[u8]> {
        self.tail_seen.set(true);
        Ok(&self.tail)
    }
}

// --- A harness that records what it saw, and how to misbehave ---

#[derive(Default)]
struct Harness {
    source: SplitSource,
    parallel: bool,
    profile: Option<ValidationProfile>,
    callbacks: Arc<Mutex<Vec<WorkerEvent>>>,
    refuse_control: bool,
    /// Return batches without validating them.
    skip: bool,
    /// Validate each function twice.
    repeat: bool,
    fail_poll: bool,
    refuse_submit: bool,
    refuse_worker: bool,
    refuse_custom: bool,
    batch_bytes: Option<usize>,
    max_batches: Option<usize>,
    peak: usize,
    submitted: usize,
    polled: usize,
    custom_base: usize,
    tail_base: usize,
    custom_offsets: Vec<(usize, usize)>,
    events: Vec<&'static str>,
    entries: Vec<(usize, usize, usize, usize)>,
    batches: Vec<(usize, Vec<u8>, usize, bool)>,
    decoded_tail: Option<Tail>,
}

impl Harness {
    fn new(bytes: &[u8]) -> Self {
        Harness {
            source: SplitSource::new(bytes),
            ..Default::default()
        }
    }

    fn with_profile(bytes: &[u8], profile: ValidationProfile) -> Self {
        Harness {
            source: SplitSource::with_profile(bytes, profile),
            profile: Some(profile),
            ..Default::default()
        }
    }

    fn validate(&mut self) -> Result<Env> {
        let source = std::mem::take(&mut self.source);
        self.tail_base = source.env.len() + source.code.len();
        let mut env = Env::new();
        let profile = self.profile.unwrap_or(ValidationProfile::Wasm1);
        let result = std::thread::scope(|threads| {
            let mut scheduler = TestScheduler::new(self, threads);
            stream::validate_streaming(1, profile, &source, &mut scheduler, &mut env)
        });
        self.source = source;
        result.map(|()| env)
    }

    /// Records custom section offsets as absolute module offsets.
    fn custom_region(&mut self, region: Region) {
        self.events.push(match region {
            Region::Environment => "environment",
            Region::Tail => "tail",
        });
        self.custom_base = match region {
            Region::Environment => 0,
            Region::Tail => self.tail_base,
        };
    }
}

impl module::ModuleVisitor for Harness {
    fn on_custom_section(&mut self, s: CustomSection) -> core::result::Result<(), VisitError> {
        self.events.push("custom");
        if self.refuse_custom {
            return Err(VisitError::OutOfMemory);
        }
        self.custom_offsets.push((
            self.custom_base + s.payload_start,
            self.custom_base + s.payload_end,
        ));
        Ok(())
    }
}

struct RefusingWorker;

impl itasca::OpVisitor for RefusingWorker {
    fn on_function_start(
        &mut self,
        _ctx: &itasca::Context,
        _type_idx: u32,
        _body_begin: usize,
        _body_end: usize,
    ) -> itasca::VisitResult {
        Err(VisitError::OutOfMemory)
    }
}

#[derive(Debug, PartialEq, Eq)]
enum WorkerEvent {
    FunctionStart(u32, usize),
    Block(BlockType),
    Loop(BlockType),
    Branch(u32, ResultType),
    BranchIf(u32, ResultType),
    I32(i32),
}

struct RecordingWorker {
    callbacks: Arc<Mutex<Vec<WorkerEvent>>>,
    refuse_control: bool,
}

impl itasca::OpVisitor for RecordingWorker {
    fn on_function_start(
        &mut self,
        ctx: &itasca::Context,
        type_idx: u32,
        _begin: usize,
        _end: usize,
    ) -> itasca::VisitResult {
        self.callbacks
            .lock()
            .unwrap()
            .push(WorkerEvent::FunctionStart(type_idx, ctx.results.len()));
        Ok(())
    }

    fn on_block(&mut self, _st: &itasca::OpIterState, bt: BlockType) -> itasca::VisitResult {
        self.callbacks.lock().unwrap().push(WorkerEvent::Block(bt));
        if self.refuse_control {
            Err(VisitError::OutOfMemory)
        } else {
            Ok(())
        }
    }

    fn on_loop(&mut self, _st: &itasca::OpIterState, bt: BlockType) -> itasca::VisitResult {
        self.callbacks.lock().unwrap().push(WorkerEvent::Loop(bt));
        Ok(())
    }

    fn on_br(
        &mut self,
        _st: &itasca::OpIterState,
        depth: u32,
        target: ResultType,
    ) -> itasca::VisitResult {
        self.callbacks
            .lock()
            .unwrap()
            .push(WorkerEvent::Branch(depth, target));
        Ok(())
    }

    fn on_br_if(
        &mut self,
        _st: &itasca::OpIterState,
        depth: u32,
        target: ResultType,
    ) -> itasca::VisitResult {
        self.callbacks
            .lock()
            .unwrap()
            .push(WorkerEvent::BranchIf(depth, target));
        Ok(())
    }

    fn on_i32_const(&mut self, _st: &itasca::OpIterState, value: i32) -> itasca::VisitResult {
        self.callbacks.lock().unwrap().push(WorkerEvent::I32(value));
        Ok(())
    }
}

/// Runs batches inline or on scoped threads, returning the newest first.
struct TestScheduler<'h, 'jobs, 'env> {
    harness: &'h mut Harness,
    threads: &'jobs Scope<'jobs, 'env>,
    pending: Vec<CodeBatch<'env>>,
    workers: Vec<ScopedJoinHandle<'jobs, CodeBatch<'env>>>,
    /// Returned by the next `poll_code_batch` instead of any submitted batch.
    foreign: Option<CodeBatch<'env>>,
}

impl<'h, 'jobs, 'env> TestScheduler<'h, 'jobs, 'env> {
    fn new(harness: &'h mut Harness, threads: &'jobs Scope<'jobs, 'env>) -> Self {
        TestScheduler {
            harness,
            threads,
            pending: Vec::new(),
            workers: Vec::new(),
            foreign: None,
        }
    }
}

impl module::ModuleVisitor for TestScheduler<'_, '_, '_> {
    fn on_custom_section(&mut self, s: CustomSection) -> core::result::Result<(), VisitError> {
        self.harness.on_custom_section(s)
    }
}

impl<'a> StreamingVisitor<'a> for TestScheduler<'_, '_, 'a> {
    fn custom_region(&mut self, region: Region) {
        self.harness.custom_region(region);
    }

    fn environment_ready(&mut self, _: &Env) -> Result<Config> {
        self.harness.events.push("ready");
        Ok(Config {
            batch_bytes: self.harness.batch_bytes.unwrap_or(4),
            max_batches: self.harness.max_batches.unwrap_or(2),
        })
    }

    fn submit_code_batch(&mut self, mut batch: CodeBatch<'a>) -> Result<()> {
        self.harness.events.push("submit");
        if self.harness.refuse_submit {
            return Err(Error::Visitor(VisitError::OutOfMemory));
        }
        assert!(!batch.is_empty());
        assert_eq!(
            batch.profile(),
            self.harness.profile.unwrap_or(ValidationProfile::Wasm1)
        );
        self.harness.batches.push((
            batch.code_offset(),
            batch.code().to_vec(),
            batch.len(),
            batch.is_last(),
        ));
        let mut indices = Vec::new();
        for _ in 0..batch.len() {
            let entry = batch.next_entry()?;
            self.harness
                .entries
                .push((entry.index, entry.start, entry.contents, entry.end));
            indices.push(entry.index);
        }
        let skip = self.harness.skip;
        let repeat = self.harness.repeat;
        let refuse = self.harness.refuse_worker;
        let refuse_control = self.harness.refuse_control;
        let callbacks = Arc::clone(&self.harness.callbacks);
        let validate = move || {
            if !skip {
                for index in indices {
                    let result = if refuse {
                        batch.validate_func(index, &mut RefusingWorker)
                    } else {
                        batch.validate_func(
                            index,
                            &mut RecordingWorker {
                                callbacks: Arc::clone(&callbacks),
                                refuse_control,
                            },
                        )
                    };
                    if let Err(error) = result {
                        // A later accepting worker cannot erase the first failure.
                        assert_eq!(batch.validate_func(index, &mut EmptyOpVisitor), Err(error));
                        break;
                    }
                    if repeat {
                        let _ = batch.validate_func(index, &mut EmptyOpVisitor);
                    }
                }
            }
            batch
        };
        if self.harness.parallel {
            self.workers.push(self.threads.spawn(validate));
        } else {
            self.pending.push(validate());
        }
        self.harness.submitted += 1;
        self.harness.peak = self
            .harness
            .peak
            .max(self.pending.len() + self.workers.len());
        Ok(())
    }

    fn poll_code_batch(&mut self) -> Result<CodeBatch<'a>> {
        self.harness.events.push("poll");
        if self.harness.fail_poll {
            return Err(Error::Host);
        }
        self.harness.polled += 1;
        if let Some(batch) = self.foreign.take() {
            return Ok(batch);
        }
        if self.harness.parallel {
            return Ok(self.workers.pop().unwrap().join().unwrap());
        }
        self.pending.pop().ok_or(Error::Host)
    }

    fn code_end(&mut self) -> Result<()> {
        self.harness.events.push("code_end");
        Ok(())
    }

    fn tail_ready(&mut self, tail: Tail) -> Result<()> {
        self.harness.events.push("tail_ready");
        self.harness.decoded_tail = Some(tail);
        Ok(())
    }
}

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
fn corpus_matches_spec_expectations() {
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
            let expected = kind == "valid";

            let contiguous = itasca::validate_module(&bytes, ValidationProfile::Wasm1);
            assert_eq!(
                contiguous.is_ok(),
                expected,
                "slice {}: {contiguous:?}; expected {kind}",
                path.display()
            );
            let mut harness = Harness::new(&bytes);
            let split = harness.validate();
            assert_eq!(
                split.is_ok(),
                expected,
                "split {}: {split:?}; expected {kind}",
                path.display()
            );
            // Check metadata transport across separate allocations. Verdicts
            // above come from the corpus, independently of either adapter.
            if let (Ok(actual), Ok(expected)) = (split, contiguous) {
                assert_eq!(actual, expected.env);
                assert_eq!(harness.decoded_tail.take().unwrap(), expected.tail);
            }
            checked += 1;
        }
    }
    assert!(checked > 1000);
}

#[test]
fn dispatched_entries_tile_the_code_region() {
    // Three entry shapes: no locals, an i64 local with an i32 parameter,
    // and a nop. The middle entry exceeds the four-byte batch target.
    let mut bytes = b"\0asm\x01\0\0\0".to_vec();
    bytes.extend([1, 9, 2, 0x60, 0, 0, 0x60, 1, 0x7f, 1, 0x7f]);
    bytes.extend([3, 4, 3, 0, 1, 0]);
    bytes.extend([
        10, 15, 3, 2, 0, 0x0b, 6, 1, 1, 0x7e, 0x20, 0, 0x0b, 3, 0, 1, 0x0b,
    ]);

    let mut harness = Harness::new(&bytes);
    let env = harness.validate().unwrap();
    assert_eq!(env.func_type_indices, vec![0, 1, 0]);
    assert_eq!(env.types.len(), 2);
    assert!(harness.decoded_tail.as_ref().unwrap().data.is_empty());
    assert_eq!(
        harness.entries,
        vec![(0, 3, 4, 6), (1, 6, 7, 13), (2, 13, 14, 17)]
    );
    assert_eq!(harness.batches.len(), 3);
    for (i, (offset, view, count, last)) in harness.batches.iter().enumerate() {
        let (_, start, _, end) = harness.entries[i];
        assert_eq!(
            (*offset, view.len(), *count, *last),
            (start, end - start, 1, i == 2)
        );
        assert_eq!(view, &harness.source.code[start..end]);
        assert!(harness.source.reads.borrow().contains(&(start, end)));
    }
    assert_eq!(
        harness.events,
        vec![
            "environment",
            "ready",
            "submit",
            "submit",
            "poll",
            "submit",
            "code_end",
            "tail",
            "tail_ready",
            "poll",
            "poll",
        ]
    );
}

#[test]
fn batch_targets_count_contents_and_allow_one_oversized_entry() {
    for (target, counts) in [
        (1, vec![1, 1, 1, 1, 1]),
        (3, vec![1, 1, 1, 1, 1]),
        (6, vec![2, 2, 1]),
        (usize::MAX, vec![5]),
    ] {
        let mut harness = Harness::new(&functions(5, 1));
        harness.batch_bytes = Some(target);
        harness.validate().unwrap();
        assert_eq!(
            harness
                .batches
                .iter()
                .map(|batch| batch.2)
                .collect::<Vec<_>>(),
            counts
        );
        assert_eq!(harness.entries.len(), 5);
        assert_eq!(harness.polled, harness.submitted);
    }
}

#[test]
fn zero_batch_configuration_rejects_before_submission() {
    for (batch_bytes, max_batches) in [(0, 1), (1, 0)] {
        let mut harness = Harness::new(&functions(1, 1));
        harness.batch_bytes = Some(batch_bytes);
        harness.max_batches = Some(max_batches);
        assert_eq!(harness.validate(), Err(Error::Host));
        assert_eq!(harness.submitted, 0);
        assert!(!harness.source.tail_seen.get());
    }
}

#[test]
fn declining_submission_stops_the_driver() {
    let bytes = functions(1, 1);
    assert!(itasca::validate_module(&bytes, ValidationProfile::Wasm1).is_ok());
    let mut harness = Harness::new(&bytes);
    harness.refuse_submit = true;
    assert_eq!(
        harness.validate(),
        Err(Error::Visitor(VisitError::OutOfMemory))
    );
    assert_eq!(harness.events, vec!["environment", "ready", "submit"]);
    assert!(harness.decoded_tail.is_none());
}

#[test]
fn declining_worker_cannot_be_overridden_by_the_scheduler() {
    let bytes = functions(1, 1);
    assert!(itasca::validate_module(&bytes, ValidationProfile::Wasm1).is_ok());
    let mut harness = Harness::new(&bytes);
    harness.refuse_worker = true;
    assert_eq!(
        harness.validate(),
        Err(Error::Body(OpError::Visitor(VisitError::OutOfMemory)))
    );
    assert_eq!((harness.submitted, harness.polled), (1, 1));
    assert!(harness.decoded_tail.is_some());
}

#[test]
fn declining_custom_hook_stops_either_region() {
    for before_code in [true, false] {
        let mut bytes = functions(1, 1);
        if before_code {
            bytes.splice(8..8, [0, 1, 0]);
        } else {
            bytes.extend([0, 1, 0]);
        }
        assert!(itasca::validate_module(&bytes, ValidationProfile::Wasm1).is_ok());
        let mut harness = Harness::new(&bytes);
        harness.refuse_custom = true;
        assert_eq!(
            harness.validate(),
            Err(Error::Visitor(VisitError::OutOfMemory))
        );
        assert_eq!(harness.submitted, usize::from(!before_code));
        assert_eq!(harness.events.last(), Some(&"custom"));
        assert!(harness.decoded_tail.is_none());
    }
}

#[test]
fn bounded_out_of_order_completion() {
    let mut harness = Harness::new(&functions(20, 1));
    harness.validate().unwrap();
    assert_eq!(harness.peak, 2);
    assert_eq!(harness.polled, harness.submitted);
    assert!(harness.source.tail_seen.get());
}

#[test]
fn parallel_batches_are_consumed_before_acceptance() {
    let mut harness = Harness::new(&functions(20, 1));
    harness.parallel = true;
    harness.validate().unwrap();
    assert_eq!(harness.polled, harness.submitted);
    assert_eq!(harness.peak, 2);
}

#[test]
fn ignored_worker_failure_remains_in_batch() {
    let mut harness = Harness::new(&functions(1, 0xff));
    assert_eq!(
        harness.validate().unwrap_err(),
        Error::Body(OpError::UnrecognizedOpcode)
    );
    assert!(harness.source.tail_seen.get());
}

#[test]
fn missing_and_repeated_validation_reject() {
    let mut harness = Harness::new(&functions(2, 1));
    harness.skip = true;
    assert_eq!(harness.validate().unwrap_err(), Error::Host);
    let mut harness = Harness::new(&functions(2, 1));
    harness.repeat = true;
    assert_eq!(harness.validate().unwrap_err(), Error::Host);
}

#[test]
fn completion_from_another_module_rejects() {
    let good = SplitSource::new(&functions(1, 1));
    let bad = SplitSource::new(&functions(1, 0xff));
    let mut good_env = Env::new();
    let mut bad_env = Env::new();
    let mut harness = Harness {
        fail_poll: true,
        ..Default::default()
    };
    std::thread::scope(|threads| {
        let mut scheduler = TestScheduler::new(&mut harness, threads);
        // Keep a genuinely validated batch from an earlier invocation.
        assert!(stream::validate_streaming(
            1,
            ValidationProfile::Wasm1,
            &good,
            &mut scheduler,
            &mut good_env
        )
        .is_err());
        scheduler.foreign = scheduler.pending.pop();
        assert!(scheduler.foreign.is_some());
        scheduler.harness.fail_poll = false;
        // Both batches have serial zero and the same function and byte ranges,
        // so only the module ID tells them apart.
        assert_eq!(
            stream::validate_streaming(
                2,
                ValidationProfile::Wasm1,
                &bad,
                &mut scheduler,
                &mut bad_env
            ),
            Err(Error::Host)
        );
    });
}

#[test]
fn every_truncated_arrival_rejects() {
    let bytes = functions(5, 1);
    let len = SplitSource::new(&bytes).code.len();
    for end in 0..len {
        let mut harness = Harness::new(&bytes);
        harness.source.early_eof = Some(end);
        assert!(harness.validate().is_err(), "end={end}");
    }
}

#[test]
fn truncated_code_allocation_reports_eof() {
    let mut harness = Harness::new(&functions(1, 1));
    harness.source.code.pop();
    assert_eq!(harness.validate().unwrap_err(), Error::UnexpectedEof);
}

#[test]
fn section_boundaries_and_tail_are_checked() {
    let bytes = functions(1, 1);
    let mut harness = Harness::new(&bytes);
    harness.source.code.push(0);
    assert_eq!(harness.validate().unwrap_err(), Error::SectionSizeMismatch);
    let mut harness = Harness::new(&bytes);
    harness.source.tail = vec![1, 0];
    assert_eq!(harness.validate().unwrap_err(), Error::SectionOutOfOrder);
    assert_eq!(harness.submitted, 1);
}

#[test]
fn caller_joins_workers_when_tail_or_input_rejects() {
    let bytes = functions(20, 1);
    let mut harness = Harness::new(&bytes);
    harness.parallel = true;
    harness.source.tail = vec![0xff];
    assert!(harness.validate().is_err());
    assert!(harness.submitted > harness.polled);
    // The scoped workers have all joined, so the same harness can validate again.
    harness.source.tail.clear();
    assert!(harness.validate().is_ok());

    let mut harness = Harness::new(&bytes);
    harness.parallel = true;
    harness.source.early_eof = Some(15);
    assert!(harness.validate().is_err());
    assert!(harness.submitted > 0);
    harness.source.early_eof = None;
    assert!(harness.validate().is_ok());
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
fn custom_section_offsets_are_region_relative() {
    for bytes in modules_with_custom_sections() {
        let mut split = Harness::new(&bytes);
        split.validate().unwrap();
        assert_eq!(
            split.custom_offsets,
            vec![(12, 14), (bytes.len() - 2, bytes.len())]
        );
        for &(start, end) in &split.custom_offsets {
            assert_eq!(&bytes[start - 1..start], b"x");
            assert_eq!(&bytes[start..end], b"yz");
        }
        let events = &split.events;
        assert_eq!(&events[..3], &["environment", "custom", "ready"]);
        let code_end = events
            .iter()
            .position(|&event| event == "code_end")
            .unwrap();
        assert_eq!(
            &events[code_end..code_end + 4],
            &["code_end", "tail", "custom", "tail_ready"]
        );
        assert!(events[code_end + 4..].iter().all(|&event| event == "poll"));
        assert_eq!(split.polled, split.submitted);
    }
}

#[test]
fn misplaced_split_rejects() {
    let mut harness = Harness::new(&functions(1, 1));
    let code = std::mem::take(&mut harness.source.code);
    harness.source.env.extend(code);
    assert_eq!(harness.validate().unwrap_err(), Error::Host);

    let no_code = &modules_with_custom_sections()[0];
    let mut harness = Harness::new(no_code);
    assert!(!harness.source.tail.is_empty());
    harness.source.code = std::mem::take(&mut harness.source.tail);
    assert_eq!(harness.validate().unwrap_err(), Error::Host);

    let mut harness = Harness::new(no_code);
    let tail = std::mem::take(&mut harness.source.tail);
    harness.source.env.extend(tail);
    assert_eq!(harness.validate().unwrap_err(), Error::Host);
}

#[test]
fn every_truncated_slice_matches_independent_validator() {
    for bytes in modules_with_custom_sections() {
        for end in 0..bytes.len() {
            let prefix = &bytes[..end];
            assert_eq!(
                itasca::validate_module(prefix, ValidationProfile::Wasm1).is_ok(),
                Validator::new_with_features(WasmFeatures::WASM1)
                    .validate_all(prefix)
                    .is_ok(),
                "truncated at {end}: {prefix:?}",
            );
        }
    }
}

fn encode(wat: &str) -> Vec<u8> {
    let buf = wast::parser::ParseBuffer::new(wat).unwrap();
    let mut module = wast::parser::parse::<wast::Wat>(&buf).unwrap();
    module.encode().unwrap()
}

#[test]
fn multivalue_profile_reaches_split_parallel_workers_and_callbacks() {
    let body = "(func (type $pair) block (type $pair) i32.const 1 i64.const 2 br 0 end)";
    let wat = format!(
        "(module (type $pair (func (result i32 i64))) {})",
        body.repeat(6)
    );
    let mut bytes = encode(&wat);
    bytes.splice(8..8, [0, 1, 0]);
    bytes.extend([0, 1, 0]);
    let mut features = WasmFeatures::WASM1;
    features.set(WasmFeatures::MULTI_VALUE, true);
    Validator::new_with_features(features)
        .validate_all(&bytes)
        .unwrap();
    assert!(itasca::validate_module(&bytes, ValidationProfile::Wasm1).is_err());
    let expected = itasca::validate_module(&bytes, ValidationProfile::MultiValue).unwrap();
    for parallel in [false, true] {
        let mut harness = Harness::with_profile(&bytes, ValidationProfile::MultiValue);
        harness.parallel = parallel;
        assert_eq!(harness.validate().unwrap(), expected.env);
        assert_eq!(harness.decoded_tail.as_ref().unwrap(), &expected.tail);
        assert_eq!((harness.submitted, harness.polled, harness.peak), (6, 6, 2));
        assert!(harness.custom_offsets.contains(&(11, 11)));
        assert!(harness.custom_offsets.contains(&(bytes.len(), bytes.len())));
        let events = harness.callbacks.lock().unwrap();
        for event in [
            WorkerEvent::FunctionStart(0, 2),
            WorkerEvent::Block(BlockType::TypeIndex(0)),
            WorkerEvent::Branch(
                0,
                ResultType::Type {
                    index: 0,
                    part: TypePart::Results,
                },
            ),
            WorkerEvent::I32(1),
        ] {
            assert_eq!(
                events.iter().filter(|seen| **seen == event).count(),
                6,
                "{event:?}"
            );
        }
    }
}

#[test]
fn multivalue_loop_callback_reports_parameter_label() {
    let bytes = encode("(module (type $loop (func (param i32) (result i64))) (func (result i64) i32.const 7 loop (type $loop) i32.const 0 br_if 0 drop i64.const 9 end))");
    let mut harness = Harness::with_profile(&bytes, ValidationProfile::MultiValue);
    harness.parallel = true;
    harness.validate().unwrap();
    let events = harness.callbacks.lock().unwrap();
    assert!(events.contains(&WorkerEvent::Loop(BlockType::TypeIndex(0))));
    assert!(events.contains(&WorkerEvent::BranchIf(
        0,
        ResultType::Type {
            index: 0,
            part: TypePart::Params
        }
    )));
}

#[test]
fn multivalue_control_callback_failure_is_sticky() {
    let bytes = encode(
        "(module (func (result i32 i64) block (result i32 i64) i32.const 1 i64.const 2 end))",
    );
    for parallel in [false, true] {
        let mut harness = Harness::with_profile(&bytes, ValidationProfile::MultiValue);
        harness.parallel = parallel;
        harness.refuse_control = true;
        assert_eq!(
            harness.validate(),
            Err(Error::Body(OpError::Visitor(VisitError::OutOfMemory)))
        );
        assert_eq!((harness.submitted, harness.polled), (1, 1));
        let events = harness.callbacks.lock().unwrap();
        assert!(matches!(events.last(), Some(WorkerEvent::Block(_))));
        assert!(!events
            .iter()
            .any(|event| matches!(event, WorkerEvent::I32(_))));
    }
}
