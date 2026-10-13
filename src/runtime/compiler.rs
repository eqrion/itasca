//! Rewrites accepted operator callbacks into immutable stack bytecode.
//!
//! This component is outside the extracted validator. A successful streaming
//! driver run validates its input; compiler correctness is tested separately.

use crate::{
    BlockType, CodeBatch, Config, Context, ElemType, Env, Error, LabelKind, MemArg, Module,
    ModuleVisitor, OpIterState, OpVisitor, Region, ResultType, Source, StackType, StreamingVisitor,
    Tail, ValidationProfile, ValueType, VisitError, VisitResult,
};
use alloc::vec::Vec;

/// Bounds on the input and aggregate compiler artifacts for one module.
///
/// Counts include every defined function. The validator's temporary metadata
/// allocations retain its documented allocator-failure limitation; these bounds
/// constrain input size and the compiler's additional storage.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CompileLimits {
    pub max_module_bytes: usize,
    pub max_functions: usize,
    pub max_types: usize,
    pub max_instructions: usize,
    pub max_branch_table_entries: usize,
    pub max_controls: usize,
    pub max_locals: usize,
}

impl Default for CompileLimits {
    fn default() -> Self {
        Self {
            max_module_bytes: 64 * 1024 * 1024,
            max_functions: 100_000,
            max_types: 100_000,
            max_instructions: 4_000_000,
            max_branch_table_entries: 1_000_000,
            max_controls: 1_000_000,
            max_locals: 4_000_000,
        }
    }
}

/// The compiler input or artifact budget that was exhausted.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CompileResource {
    ModuleBytes,
    Functions,
    Types,
    Instructions,
    BranchTableEntries,
    Controls,
    Locals,
    Allocation,
}

/// A validation failure or an explicit compiler resource limit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CompileError {
    Validation(Error),
    Resource(CompileResource),
}

impl core::fmt::Display for CompileError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Validation(error) => error.fmt(f),
            Self::Resource(resource) => write!(f, "compiler resource exhausted: {resource:?}"),
        }
    }
}
#[cfg(feature = "std")]
impl std::error::Error for CompileError {}

struct Budget {
    limits: CompileLimits,
    instructions: usize,
    branches: usize,
    controls: usize,
    locals: usize,
    error: Option<CompileResource>,
}
impl Budget {
    fn reject(&mut self, resource: CompileResource) -> VisitError {
        self.error = Some(resource);
        VisitError::OutOfMemory
    }
    fn charge(&mut self, resource: CompileResource) -> VisitResult {
        let (used, limit) = match resource {
            CompileResource::Instructions => (&mut self.instructions, self.limits.max_instructions),
            CompileResource::BranchTableEntries => {
                (&mut self.branches, self.limits.max_branch_table_entries)
            }
            CompileResource::Controls => (&mut self.controls, self.limits.max_controls),
            CompileResource::Locals => (&mut self.locals, self.limits.max_locals),
            _ => unreachable!("only artifact counters are charged"),
        };
        if *used >= limit {
            return Err(self.reject(resource));
        }
        *used += 1;
        Ok(())
    }
    fn push<T>(&mut self, values: &mut Vec<T>, value: T) -> VisitResult {
        values
            .try_reserve(1)
            .map_err(|_| self.reject(CompileResource::Allocation))?;
        values.push(value);
        Ok(())
    }
}

/// Validated metadata and immutable executable code, independent of any instance.
///
/// Constructed only after the entire validation driver accepts, including its
/// tail and every issued worker. The rewriting and execution are not verified
/// by the validator's Lean theorems.
#[derive(Debug)]
pub struct ExecutableModule {
    pub(super) module: Module,
    pub(super) profile: ValidationProfile,
    pub(super) functions: Vec<CompiledFunction>,
}

/// Sizes and original module byte coordinates of one defined function.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FunctionStats {
    pub type_index: u32,
    /// Parameters and declared locals combined.
    pub local_count: usize,
    /// Maximum operand depth on a structurally reachable path.
    pub max_stack: usize,
    pub instruction_count: usize,
    /// Byte size of live instruction entries, excluding vector spare capacity.
    pub instruction_bytes: usize,
    pub branch_table_entries: usize,
    /// Byte size of live branch-table entries, excluding vector spare capacity.
    pub branch_table_bytes: usize,
    /// Inclusive instruction-body start, relative to the complete input module.
    pub body_start: usize,
    /// Exclusive instruction-body end, relative to the complete input module.
    pub body_end: usize,
}

/// A structured label's source extent and rewritten continuation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ControlMap {
    pub kind: LabelKind,
    /// The opening operator's complete-module byte offset, or the first body
    /// opcode for the synthetic function label.
    pub source_start: usize,
    /// The byte after the closing `end`, relative to the complete module.
    pub source_end: usize,
    /// The first bytecode PC in the construct's body.
    pub start_pc: usize,
    /// Continuation PC after the construct, or the function's final return PC.
    pub end_pc: usize,
    pub stack_height: usize,
    pub parameters: usize,
    pub results: usize,
}

impl ExecutableModule {
    /// Returns validated module declarations and index spaces.
    pub fn env(&self) -> &Env {
        self.module.env()
    }
    /// Returns validated data-segment initialization information.
    pub fn tail(&self) -> &Tail {
        self.module.tail()
    }
    /// Returns the language profile used during compilation.
    pub fn profile(&self) -> ValidationProfile {
        self.profile
    }
    /// Returns the number of defined functions, excluding imported functions.
    pub fn function_count(&self) -> usize {
        self.functions.len()
    }
    /// Returns bounds for a defined-function index, excluding imports.
    pub fn function_stats(&self, index: usize) -> Option<FunctionStats> {
        let f = self.functions.get(index)?;
        Some(FunctionStats {
            type_index: f.type_index,
            local_count: f.locals.len(),
            max_stack: f.max_stack,
            instruction_count: f.instructions.len(),
            instruction_bytes: f.instructions.len() * core::mem::size_of::<Instruction>(),
            branch_table_entries: f.branches.len(),
            branch_table_bytes: f.branches.len() * core::mem::size_of::<Branch>(),
            body_start: f.body_start,
            body_end: f.body_end,
        })
    }
    /// Maps bytecode PCs to original opcode offsets in the complete module.
    ///
    /// `index` is a defined-function index, excluding imports. Eliminated
    /// structural operators are represented in `function_control_map`.
    pub fn function_source_offsets(&self, index: usize) -> Option<&[usize]> {
        Some(&self.functions.get(index)?.source_offsets)
    }
    /// Returns structured labels in opening order for a defined-function index.
    pub fn function_control_map(&self, index: usize) -> Option<&[ControlMap]> {
        Some(&self.functions.get(index)?.controls)
    }
}

#[derive(Debug)]
pub(super) struct CompiledFunction {
    pub(super) locals: Vec<ValueType>,
    pub(super) max_stack: usize,
    pub(super) instructions: Vec<Instruction>,
    pub(super) branches: Vec<Branch>,
    pub(super) source_offsets: Vec<usize>,
    controls: Vec<ControlMap>,
    type_index: u32,
    body_start: usize,
    body_end: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Branch {
    pub(super) target: usize,
    pub(super) height: usize,
    pub(super) keep: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Instruction {
    Op {
        opcode: u16,
        a: u32,
        b: u32,
        bits: u128,
    },
    Jump(Branch),
    JumpIf(Branch),
    JumpIfZero(usize),
    /// Entries include the default target last; `len` includes that entry.
    JumpTable {
        start: usize,
        len: usize,
    },
    Return,
}

impl CompiledFunction {
    // A final independent structural gate catches unresolved or out-of-range
    // fixups before any executable is published. Stack typing and compiler
    // correspondence are separate obligations, including unreachable code.
    fn well_formed(&self) -> bool {
        let length = self.instructions.len();
        if length == 0
            || self.source_offsets.len() != length
            || self.instructions[length - 1] != Instruction::Return
        {
            return false;
        }
        let mut index = 0;
        while index < length {
            let source = self.source_offsets[index];
            if source < self.body_start || source >= self.body_end {
                return false;
            }
            if index > 0 && self.source_offsets[index - 1] >= source {
                return false;
            }
            match self.instructions[index] {
                Instruction::Jump(branch) | Instruction::JumpIf(branch) => {
                    if branch.target >= length {
                        return false;
                    }
                }
                Instruction::JumpIfZero(target) => {
                    if target >= length {
                        return false;
                    }
                }
                Instruction::JumpTable { start, len } => {
                    if len == 0 || start > self.branches.len() || len > self.branches.len() - start
                    {
                        return false;
                    }
                }
                _ => {}
            }
            index += 1;
        }
        index = 0;
        while index < self.branches.len() {
            if self.branches[index].target >= length {
                return false;
            }
            index += 1;
        }
        index = 0;
        while index < self.controls.len() {
            let map = &self.controls[index];
            if map.start_pc > map.end_pc
                || map.end_pc >= length
                || map.source_start < self.body_start
                || map.source_end > self.body_end
                || map.source_start >= map.source_end
            {
                return false;
            }
            index += 1;
        }
        true
    }
}

/// Validates and rewrites a complete module under the selected profile.
///
/// The returned code owns all initialization bytes and has no dependency on the
/// input slice. The default `CompileLimits` apply. Resource failures are reported
/// as `Error::Visitor(VisitError::OutOfMemory)`; use `compile_with_limits` to
/// distinguish the exhausted compiler budget from validation failures.
pub fn compile(bytes: &[u8], profile: ValidationProfile) -> Result<ExecutableModule, Error> {
    match compile_with_limits(bytes, profile, CompileLimits::default()) {
        Ok(module) => Ok(module),
        Err(CompileError::Validation(error)) => Err(error),
        Err(CompileError::Resource(_)) => Err(Error::Visitor(VisitError::OutOfMemory)),
    }
}

/// Validates and rewrites a complete module with explicit compiler budgets.
///
/// Bytecode, source maps, locals, labels, and branch-table storage are bounded;
/// compiler allocations use fallible reservation. Metadata decoding retains the
/// validator's documented allocation premise. A resource failure never yields a
/// partial executable module.
pub fn compile_with_limits(
    bytes: &[u8],
    profile: ValidationProfile,
    limits: CompileLimits,
) -> Result<ExecutableModule, CompileError> {
    if bytes.len() > limits.max_module_bytes {
        return Err(CompileError::Resource(CompileResource::ModuleBytes));
    }
    let (code_start, code_end) = code_region(bytes);
    let source = CompileSource {
        bytes,
        code_start,
        code_end,
    };
    let mut env = Env::new();
    let mut scheduler = CompileScheduler {
        signatures: Vec::new(),
        completed: Vec::new(),
        functions: Vec::new(),
        tail: None,
        code_start,
        budget: Budget {
            limits,
            instructions: 0,
            branches: 0,
            controls: 0,
            locals: 0,
            error: None,
        },
    };
    // Batches never leave this invocation's private scheduler, so ID zero is
    // unique among all batches that can reach it, even across concurrent calls.
    if let Err(error) = crate::validate_streaming(0, profile, &source, &mut scheduler, &mut env) {
        return Err(match scheduler.budget.error {
            Some(resource) => CompileError::Resource(resource),
            None => CompileError::Validation(error),
        });
    }
    let mut functions = Vec::new();
    let mut index = 0;
    while index < scheduler.functions.len() {
        let function = scheduler.functions[index]
            .take()
            .ok_or(CompileError::Validation(Error::Host))?;
        scheduler
            .budget
            .push(&mut functions, function)
            .map_err(|_| CompileError::Resource(CompileResource::Allocation))?;
        index += 1;
    }
    let tail = scheduler
        .tail
        .take()
        .ok_or(CompileError::Validation(Error::Host))?;
    // Release all source/environment borrows before publishing owned metadata.
    drop(scheduler);
    Ok(ExecutableModule {
        module: Module { env, tail },
        profile,
        functions,
    })
}

fn code_region(bytes: &[u8]) -> (usize, usize) {
    let mut pos = 8;
    while pos < bytes.len() {
        let id = bytes[pos];
        if id > 10 && id != 12 {
            return (pos, pos);
        }
        let end = match crate::reader::read_u32_leb(bytes, pos + 1) {
            Ok((len, contents)) => contents + (len as usize).min(bytes.len() - contents),
            Err(_) => bytes.len(),
        };
        if id == 10 {
            return (pos, end);
        }
        pos = end;
    }
    (bytes.len(), bytes.len())
}

struct CompileSource<'a> {
    bytes: &'a [u8],
    code_start: usize,
    code_end: usize,
}
impl Source for CompileSource<'_> {
    fn environment(&self) -> Result<&[u8], Error> {
        Ok(&self.bytes[..self.code_start])
    }
    fn code_len(&self) -> usize {
        self.code_end - self.code_start
    }
    fn code(&self, start: usize, end: usize) -> Result<&[u8], Error> {
        if start > end || end > self.code_len() {
            return Err(Error::Host);
        }
        Ok(&self.bytes[self.code_start + start..self.code_start + end])
    }
    fn tail(&self) -> Result<&[u8], Error> {
        Ok(&self.bytes[self.code_end..])
    }
}

struct CompileScheduler<'a> {
    signatures: Vec<(usize, usize)>,
    completed: Vec<CodeBatch<'a>>,
    functions: Vec<Option<CompiledFunction>>,
    tail: Option<Tail>,
    code_start: usize,
    budget: Budget,
}
impl ModuleVisitor for CompileScheduler<'_> {}
impl<'a> StreamingVisitor<'a> for CompileScheduler<'a> {
    fn custom_region(&mut self, _region: Region) {}
    fn environment_ready(&mut self, env: &Env) -> Result<Config, Error> {
        if env.func_type_indices().len() > self.budget.limits.max_functions {
            return Err(Error::Visitor(
                self.budget.reject(CompileResource::Functions),
            ));
        }
        if env.types().len() > self.budget.limits.max_types {
            return Err(Error::Visitor(self.budget.reject(CompileResource::Types)));
        }
        let mut i = 0;
        while i < env.types().len() {
            let signature = &env.types()[i];
            self.budget
                .push(
                    &mut self.signatures,
                    (signature.params.len(), signature.results.len()),
                )
                .map_err(Error::Visitor)?;
            i += 1;
        }
        i = 0;
        while i < env.func_type_indices().len() {
            self.budget
                .push(&mut self.functions, None)
                .map_err(Error::Visitor)?;
            i += 1;
        }
        Ok(Config {
            batch_bytes: 25_000,
            max_batches: 4,
        })
    }
    fn submit_code_batch(&mut self, mut batch: CodeBatch<'a>) -> Result<(), Error> {
        let mut i = 0;
        while i < batch.len() {
            let entry = batch.next_entry()?;
            let mut compiler = FunctionCompiler::new(
                &self.signatures,
                &mut self.budget,
                self.code_start + batch.code_offset(),
            );
            batch.validate_func(entry.index, &mut compiler)?;
            let function = compiler.finish()?;
            let destination = self.functions.get_mut(entry.index).ok_or(Error::Host)?;
            if destination.is_some() {
                return Err(Error::Host);
            }
            *destination = Some(function);
            i += 1;
        }
        self.budget
            .push(&mut self.completed, batch)
            .map_err(Error::Visitor)?;
        Ok(())
    }
    fn poll_code_batch(&mut self) -> Result<CodeBatch<'a>, Error> {
        // Deliberately retire in reverse completion order: artifact assembly
        // depends on the issued function identity, never the poll order.
        self.completed.pop().ok_or(Error::Host)
    }
    fn code_end(&mut self) -> Result<(), Error> {
        Ok(())
    }
    fn tail_ready(&mut self, tail: Tail) -> Result<(), Error> {
        self.tail = Some(tail);
        Ok(())
    }
}

#[derive(Clone, Copy)]
enum Fixup {
    Instruction(usize),
    Table(usize),
}
struct Frame {
    map: usize,
    kind: LabelKind,
    height: usize,
    params: usize,
    results: usize,
    start_pc: usize,
    if_pc: Option<usize>,
    entry_reachable: bool,
    end_reachable: bool,
    fixups: Vec<Fixup>,
}

struct FunctionCompiler<'a> {
    signatures: &'a [(usize, usize)],
    budget: &'a mut Budget,
    batch_start: usize,
    function: CompiledFunction,
    frames: Vec<Frame>,
    reachable: bool,
    next_source: usize,
    table_start: usize,
}

impl<'a> FunctionCompiler<'a> {
    fn new(signatures: &'a [(usize, usize)], budget: &'a mut Budget, batch_start: usize) -> Self {
        Self {
            signatures,
            budget,
            batch_start,
            function: CompiledFunction {
                locals: Vec::new(),
                max_stack: 0,
                instructions: Vec::new(),
                branches: Vec::new(),
                source_offsets: Vec::new(),
                controls: Vec::new(),
                type_index: 0,
                body_start: 0,
                body_end: 0,
            },
            frames: Vec::new(),
            reachable: true,
            next_source: 0,
            table_start: 0,
        }
    }
    fn finish(self) -> Result<CompiledFunction, Error> {
        if !self.frames.is_empty() || !self.function.well_formed() {
            return Err(Error::Host);
        }
        Ok(self.function)
    }
    fn emit(&mut self, instruction: Instruction) -> VisitResult {
        self.budget.charge(CompileResource::Instructions)?;
        self.budget
            .push(&mut self.function.instructions, instruction)?;
        self.budget.push(
            &mut self.function.source_offsets,
            self.function.body_start + self.next_source,
        )
    }
    fn observe(&mut self, st: &OpIterState) {
        if self.reachable {
            self.function.max_stack = self.function.max_stack.max(st.vals.len());
        }
        self.next_source = st.pos;
    }
    fn op(&mut self, st: &OpIterState, opcode: u16, a: u32, b: u32, bits: u128) -> VisitResult {
        self.emit(Instruction::Op { opcode, a, b, bits })?;
        self.observe(st);
        Ok(())
    }
    fn enter(&mut self, st: &OpIterState, kind: LabelKind, bt: BlockType) -> VisitResult {
        let height = st.ctrls.last().expect("validated frame").value_stack_base;
        let (params, results) = match bt {
            BlockType::Empty => (0, 0),
            BlockType::Value(_) => (0, 1),
            BlockType::TypeIndex(index) => self.signatures[index as usize],
        };
        let source_start = self.function.body_start + self.next_source;
        let if_pc = if kind == LabelKind::Then {
            let pc = self.function.instructions.len();
            self.emit(Instruction::JumpIfZero(usize::MAX))?;
            Some(pc)
        } else {
            None
        };
        let start_pc = self.function.instructions.len();
        let map = self.function.controls.len();
        self.budget.charge(CompileResource::Controls)?;
        self.budget.push(
            &mut self.function.controls,
            ControlMap {
                kind,
                source_start,
                source_end: 0,
                start_pc,
                end_pc: 0,
                stack_height: height,
                parameters: params,
                results,
            },
        )?;
        self.budget.push(
            &mut self.frames,
            Frame {
                map,
                kind,
                height,
                params,
                results,
                start_pc,
                if_pc,
                entry_reachable: self.reachable,
                end_reachable: false,
                fixups: Vec::new(),
            },
        )?;
        self.observe(st);
        Ok(())
    }
    fn branch(&mut self, depth: u32, site: Fixup) -> Result<Branch, VisitError> {
        let index = self.frames.len() - 1 - depth as usize;
        let frame = &mut self.frames[index];
        let is_loop = frame.kind == LabelKind::Loop;
        if !is_loop {
            self.budget.push(&mut frame.fixups, site)?;
            frame.end_reachable |= self.reachable;
        }
        Ok(Branch {
            target: if is_loop { frame.start_pc } else { usize::MAX },
            height: frame.height,
            keep: if is_loop { frame.params } else { frame.results },
        })
    }
    fn patch(&mut self, site: Fixup, target: usize) {
        match site {
            Fixup::Instruction(pc) => match &mut self.function.instructions[pc] {
                Instruction::Jump(branch) | Instruction::JumpIf(branch) => branch.target = target,
                _ => unreachable!("only branch instructions have branch fixups"),
            },
            Fixup::Table(index) => self.function.branches[index].target = target,
        }
    }
}

macro_rules! simple_hooks {
    ($($name:ident => $opcode:expr;)*) => { $(
        fn $name(&mut self, st: &OpIterState) -> VisitResult { self.op(st, $opcode, 0, 0, 0) }
    )* };
}
macro_rules! index_hooks {
    ($($name:ident => $opcode:expr;)*) => { $(
        fn $name(&mut self, st: &OpIterState, index: u32) -> VisitResult {
            self.op(st, $opcode, index, 0, 0)
        }
    )* };
}
macro_rules! memory_hooks {
    ($($name:ident => $opcode:expr;)*) => { $(
        fn $name(&mut self, st: &OpIterState, arg: MemArg) -> VisitResult {
            self.op(st, $opcode, arg.offset, arg.align, 0)
        }
    )* };
}

impl OpVisitor for FunctionCompiler<'_> {
    fn on_function_start(
        &mut self,
        ctx: &Context,
        type_idx: u32,
        body_begin: usize,
        body_end: usize,
    ) -> VisitResult {
        self.function.type_index = type_idx;
        self.function.body_start = self.batch_start + body_begin;
        self.function.body_end = self.batch_start + body_end;
        let mut index = 0;
        while index < ctx.locals.len() {
            self.budget.charge(CompileResource::Locals)?;
            self.budget
                .push(&mut self.function.locals, ctx.locals[index])?;
            index += 1;
        }
        self.budget.charge(CompileResource::Controls)?;
        self.budget.push(
            &mut self.function.controls,
            ControlMap {
                kind: LabelKind::Body,
                source_start: self.function.body_start,
                source_end: 0,
                start_pc: 0,
                end_pc: 0,
                stack_height: 0,
                parameters: 0,
                results: ctx.results.len(),
            },
        )?;
        self.budget.push(
            &mut self.frames,
            Frame {
                map: 0,
                kind: LabelKind::Body,
                height: 0,
                params: 0,
                results: ctx.results.len(),
                start_pc: 0,
                if_pc: None,
                entry_reachable: true,
                end_reachable: false,
                fixups: Vec::new(),
            },
        )?;
        Ok(())
    }
    fn on_block(&mut self, st: &OpIterState, bt: BlockType) -> VisitResult {
        self.enter(st, LabelKind::Block, bt)
    }
    fn on_loop(&mut self, st: &OpIterState, bt: BlockType) -> VisitResult {
        self.enter(st, LabelKind::Loop, bt)
    }
    fn on_if(&mut self, st: &OpIterState, bt: BlockType) -> VisitResult {
        self.enter(st, LabelKind::Then, bt)
    }
    fn on_else(&mut self, st: &OpIterState, _bt: BlockType) -> VisitResult {
        let pc = self.function.instructions.len();
        let frame = self.frames.last_mut().expect("validated else frame");
        frame.end_reachable |= self.reachable;
        self.reachable = frame.entry_reachable;
        frame.kind = LabelKind::Else;
        self.budget
            .push(&mut frame.fixups, Fixup::Instruction(pc))?;
        let branch = Branch {
            target: usize::MAX,
            height: frame.height,
            keep: frame.results,
        };
        let if_pc = frame.if_pc.take().expect("if condition");
        self.emit(Instruction::Jump(branch))?;
        self.function.instructions[if_pc] = Instruction::JumpIfZero(pc + 1);
        self.observe(st);
        Ok(())
    }
    fn on_end(&mut self, st: &OpIterState, _kind: LabelKind, _bt: BlockType) -> VisitResult {
        let frame = self.frames.pop().expect("validated end frame");
        let target = self.function.instructions.len();
        if let Some(if_pc) = frame.if_pc {
            self.function.instructions[if_pc] = Instruction::JumpIfZero(target);
        }
        let mut i = 0;
        while i < frame.fixups.len() {
            self.patch(frame.fixups[i], target);
            i += 1;
        }
        let map = &mut self.function.controls[frame.map];
        map.end_pc = target;
        map.source_end = self.function.body_start + st.pos;
        self.reachable = self.reachable
            || frame.end_reachable
            || (frame.kind == LabelKind::Then && frame.entry_reachable);
        if frame.kind == LabelKind::Body {
            self.emit(Instruction::Return)?;
        }
        self.observe(st);
        Ok(())
    }
    fn on_br(&mut self, st: &OpIterState, depth: u32, _types: ResultType) -> VisitResult {
        let branch = self.branch(depth, Fixup::Instruction(self.function.instructions.len()))?;
        self.emit(Instruction::Jump(branch))?;
        self.reachable = false;
        self.observe(st);
        Ok(())
    }
    fn on_br_if(&mut self, st: &OpIterState, depth: u32, _types: ResultType) -> VisitResult {
        let branch = self.branch(depth, Fixup::Instruction(self.function.instructions.len()))?;
        self.emit(Instruction::JumpIf(branch))?;
        self.observe(st);
        Ok(())
    }
    fn on_br_table_label(&mut self, _st: &OpIterState, depth: u32) -> VisitResult {
        self.budget.charge(CompileResource::BranchTableEntries)?;
        let branch = self.branch(depth, Fixup::Table(self.function.branches.len()))?;
        self.budget.push(&mut self.function.branches, branch)?;
        Ok(())
    }
    fn on_br_table(&mut self, st: &OpIterState, default: u32, _types: ResultType) -> VisitResult {
        self.on_br_table_label(st, default)?;
        let end = self.function.branches.len();
        self.emit(Instruction::JumpTable {
            start: self.table_start,
            len: end - self.table_start,
        })?;
        self.table_start = end;
        self.reachable = false;
        self.observe(st);
        Ok(())
    }
    fn on_return(&mut self, st: &OpIterState) -> VisitResult {
        self.emit(Instruction::Return)?;
        self.reachable = false;
        self.observe(st);
        Ok(())
    }
    fn on_unreachable(&mut self, st: &OpIterState) -> VisitResult {
        self.reachable = false;
        self.op(st, 0x00, 0, 0, 0)
    }
    fn on_call_indirect(&mut self, st: &OpIterState, type_idx: u32, table_idx: u32) -> VisitResult {
        self.op(st, 0x11, type_idx, table_idx, 0)
    }
    fn on_drop(&mut self, st: &OpIterState, _ty: StackType) -> VisitResult {
        self.op(st, 0x1a, 0, 0, 0)
    }
    fn on_select(&mut self, st: &OpIterState, _ty: StackType) -> VisitResult {
        self.op(st, 0x1b, 0, 0, 0)
    }
    fn on_select_typed(&mut self, st: &OpIterState, _ty: ValueType) -> VisitResult {
        self.op(st, 0x1c, 0, 0, 0)
    }
    fn on_i32_const(&mut self, st: &OpIterState, v: i32) -> VisitResult {
        self.op(st, 0x41, 0, 0, v as u32 as u128)
    }
    fn on_i64_const(&mut self, st: &OpIterState, v: i64) -> VisitResult {
        self.op(st, 0x42, 0, 0, v as u64 as u128)
    }
    fn on_f32_const(&mut self, st: &OpIterState, bits: u32) -> VisitResult {
        self.op(st, 0x43, 0, 0, bits as u128)
    }
    fn on_f64_const(&mut self, st: &OpIterState, bits: u64) -> VisitResult {
        self.op(st, 0x44, 0, 0, bits as u128)
    }
    fn on_ref_null(&mut self, st: &OpIterState, ty: ElemType) -> VisitResult {
        self.op(st, 0xd0, if ty == ElemType::FuncRef { 0 } else { 1 }, 0, 0)
    }
    fn on_table_init(&mut self, st: &OpIterState, element: u32, table: u32) -> VisitResult {
        self.op(st, 0x10c, element, table, 0)
    }
    fn on_table_copy(&mut self, st: &OpIterState, destination: u32, source: u32) -> VisitResult {
        self.op(st, 0x10e, destination, source, 0)
    }
    fn on_simd(&mut self, st: &OpIterState, subopcode: u32) -> VisitResult {
        self.op(st, 0x200 + subopcode as u16, 0, 0, 0)
    }
    fn on_simd_lane(&mut self, st: &OpIterState, subopcode: u32, lane: u8) -> VisitResult {
        self.op(st, 0x200 + subopcode as u16, lane as u32, 0, 0)
    }
    fn on_simd_memory(&mut self, st: &OpIterState, subopcode: u32, arg: MemArg) -> VisitResult {
        self.op(st, 0x200 + subopcode as u16, arg.offset, arg.align, 0)
    }
    fn on_simd_memory_lane(
        &mut self,
        st: &OpIterState,
        subopcode: u32,
        arg: MemArg,
        lane: u8,
    ) -> VisitResult {
        self.op(
            st,
            0x200 + subopcode as u16,
            arg.offset,
            arg.align,
            lane as u128,
        )
    }
    fn on_simd_const(&mut self, st: &OpIterState, low: u64, high: u64) -> VisitResult {
        self.op(st, 0x20c, 0, 0, low as u128 | ((high as u128) << 64))
    }
    fn on_simd_shuffle(&mut self, st: &OpIterState, low: u64, high: u64) -> VisitResult {
        self.op(st, 0x20d, 0, 0, low as u128 | ((high as u128) << 64))
    }

    index_hooks! {
        on_call => 0x10;
        on_local_get => 0x20; on_local_set => 0x21; on_local_tee => 0x22;
        on_global_get => 0x23; on_global_set => 0x24;
        on_table_get => 0x25; on_table_set => 0x26;
        on_ref_func => 0xd2;
        on_memory_init => 0x108; on_data_drop => 0x109;
        on_elem_drop => 0x10d; on_table_grow => 0x10f;
        on_table_size => 0x110; on_table_fill => 0x111;
    }
    simple_hooks! {
        on_nop => 0x01; on_memory_size => 0x3f; on_memory_grow => 0x40;
        on_ref_is_null => 0xd1;
        on_memory_copy => 0x10a; on_memory_fill => 0x10b;
        on_i32_extend8_s => 0xc0; on_i32_extend16_s => 0xc1;
        on_i64_extend8_s => 0xc2; on_i64_extend16_s => 0xc3; on_i64_extend32_s => 0xc4;
        on_i32_trunc_sat_f32_s => 0x100; on_i32_trunc_sat_f32_u => 0x101;
        on_i32_trunc_sat_f64_s => 0x102; on_i32_trunc_sat_f64_u => 0x103;
        on_i64_trunc_sat_f32_s => 0x104; on_i64_trunc_sat_f32_u => 0x105;
        on_i64_trunc_sat_f64_s => 0x106; on_i64_trunc_sat_f64_u => 0x107;
    }
    simple_hooks! {
        on_i32_eqz => 0x45;
        on_i32_eq => 0x46;
        on_i32_ne => 0x47;
        on_i32_lt_s => 0x48;
        on_i32_lt_u => 0x49;
        on_i32_gt_s => 0x4a;
        on_i32_gt_u => 0x4b;
        on_i32_le_s => 0x4c;
        on_i32_le_u => 0x4d;
        on_i32_ge_s => 0x4e;
        on_i32_ge_u => 0x4f;
        on_i64_eqz => 0x50;
        on_i64_eq => 0x51;
        on_i64_ne => 0x52;
        on_i64_lt_s => 0x53;
        on_i64_lt_u => 0x54;
        on_i64_gt_s => 0x55;
        on_i64_gt_u => 0x56;
        on_i64_le_s => 0x57;
        on_i64_le_u => 0x58;
        on_i64_ge_s => 0x59;
        on_i64_ge_u => 0x5a;
        on_f32_eq => 0x5b;
        on_f32_ne => 0x5c;
        on_f32_lt => 0x5d;
        on_f32_gt => 0x5e;
        on_f32_le => 0x5f;
        on_f32_ge => 0x60;
        on_f64_eq => 0x61;
        on_f64_ne => 0x62;
        on_f64_lt => 0x63;
        on_f64_gt => 0x64;
        on_f64_le => 0x65;
        on_f64_ge => 0x66;
        on_i32_sub => 0x6b;
        on_i32_mul => 0x6c;
        on_i32_div_s => 0x6d;
        on_i32_div_u => 0x6e;
        on_i32_rem_s => 0x6f;
        on_i32_rem_u => 0x70;
        on_i32_and => 0x71;
        on_i32_or => 0x72;
        on_i32_xor => 0x73;
        on_i32_shl => 0x74;
        on_i32_shr_s => 0x75;
        on_i32_shr_u => 0x76;
        on_i32_rotl => 0x77;
        on_i32_rotr => 0x78;
        on_i64_add => 0x7c;
        on_i64_sub => 0x7d;
        on_i64_mul => 0x7e;
        on_i64_div_s => 0x7f;
        on_i64_div_u => 0x80;
        on_i64_rem_s => 0x81;
        on_i64_rem_u => 0x82;
        on_i64_and => 0x83;
        on_i64_or => 0x84;
        on_i64_xor => 0x85;
        on_i64_shl => 0x86;
        on_i64_shr_s => 0x87;
        on_i64_shr_u => 0x88;
        on_i64_rotl => 0x89;
        on_i64_rotr => 0x8a;
        on_f32_add => 0x92;
        on_f32_sub => 0x93;
        on_f32_mul => 0x94;
        on_f32_div => 0x95;
        on_f32_min => 0x96;
        on_f32_max => 0x97;
        on_f32_copysign => 0x98;
        on_f64_add => 0xa0;
        on_f64_sub => 0xa1;
        on_f64_mul => 0xa2;
        on_f64_div => 0xa3;
        on_f64_min => 0xa4;
        on_f64_max => 0xa5;
        on_f64_copysign => 0xa6;
        on_i32_clz => 0x67;
        on_i32_ctz => 0x68;
        on_i32_popcnt => 0x69;
        on_i32_add => 0x6a;
        on_i64_clz => 0x79;
        on_i64_ctz => 0x7a;
        on_i64_popcnt => 0x7b;
        on_f32_abs => 0x8b;
        on_f32_neg => 0x8c;
        on_f32_ceil => 0x8d;
        on_f32_floor => 0x8e;
        on_f32_trunc => 0x8f;
        on_f32_nearest => 0x90;
        on_f32_sqrt => 0x91;
        on_f64_abs => 0x99;
        on_f64_neg => 0x9a;
        on_f64_ceil => 0x9b;
        on_f64_floor => 0x9c;
        on_f64_trunc => 0x9d;
        on_f64_nearest => 0x9e;
        on_f64_sqrt => 0x9f;
        on_i32_wrap_i64 => 0xa7;
        on_i32_trunc_f32_s => 0xa8;
        on_i32_trunc_f32_u => 0xa9;
        on_i32_trunc_f64_s => 0xaa;
        on_i32_trunc_f64_u => 0xab;
        on_i64_extend_i32_s => 0xac;
        on_i64_extend_i32_u => 0xad;
        on_i64_trunc_f32_s => 0xae;
        on_i64_trunc_f32_u => 0xaf;
        on_i64_trunc_f64_s => 0xb0;
        on_i64_trunc_f64_u => 0xb1;
        on_f32_convert_i32_s => 0xb2;
        on_f32_convert_i32_u => 0xb3;
        on_f32_convert_i64_s => 0xb4;
        on_f32_convert_i64_u => 0xb5;
        on_f32_demote_f64 => 0xb6;
        on_f64_convert_i32_s => 0xb7;
        on_f64_convert_i32_u => 0xb8;
        on_f64_convert_i64_s => 0xb9;
        on_f64_convert_i64_u => 0xba;
        on_f64_promote_f32 => 0xbb;
        on_i32_reinterpret_f32 => 0xbc;
        on_i64_reinterpret_f64 => 0xbd;
        on_f32_reinterpret_i32 => 0xbe;
        on_f64_reinterpret_i64 => 0xbf;
    }
    memory_hooks! {
        on_i32_load => 0x28;
        on_i64_load => 0x29;
        on_f32_load => 0x2a;
        on_f64_load => 0x2b;
        on_i32_load8_s => 0x2c;
        on_i32_load8_u => 0x2d;
        on_i32_load16_s => 0x2e;
        on_i32_load16_u => 0x2f;
        on_i64_load8_s => 0x30;
        on_i64_load8_u => 0x31;
        on_i64_load16_s => 0x32;
        on_i64_load16_u => 0x33;
        on_i64_load32_s => 0x34;
        on_i64_load32_u => 0x35;
        on_i32_store => 0x36;
        on_i64_store => 0x37;
        on_f32_store => 0x38;
        on_f64_store => 0x39;
        on_i32_store8 => 0x3a;
        on_i32_store16 => 0x3b;
        on_i64_store8 => 0x3c;
        on_i64_store16 => 0x3d;
        on_i64_store32 => 0x3e;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn module(source: &str) -> ExecutableModule {
        let buffer = wast::parser::ParseBuffer::new(source).unwrap();
        let bytes = wast::parser::parse::<wast::Wat>(&buffer)
            .unwrap()
            .encode()
            .unwrap();
        compile(&bytes, ValidationProfile::Wasm2).unwrap()
    }

    #[test]
    fn loop_branches_keep_parameters_and_block_branches_keep_results() {
        let module = module(
            "(module (func (result i32 i64)
            (block (result i32 i64)
                i32.const 10 i64.const 20
                (loop (param i32 i64) (result i32 i64)
                    i32.const 0 br_if 0
                    br 1))))",
        );
        let f = &module.functions[0];
        assert_eq!(f.max_stack, 3);
        assert_eq!(
            f.instructions[3],
            Instruction::JumpIf(Branch {
                target: 2,
                height: 0,
                keep: 2
            })
        );
        assert_eq!(
            f.instructions[4],
            Instruction::Jump(Branch {
                target: 5,
                height: 0,
                keep: 2
            })
        );
        assert_eq!(f.instructions[5], Instruction::Return);
        assert_eq!(f.controls[2].parameters, 2);
        assert_eq!(f.controls[2].start_pc, 2);
    }

    #[test]
    fn table_targets_have_independent_stack_adjustments() {
        let module = module(
            "(module (func (param i32) (result i32)
            (block (result i32)
                i64.const 9
                (block (result i32)
                    i32.const 7 local.get 0 br_table 0 1)
                return)))",
        );
        let f = &module.functions[0];
        assert_eq!(
            f.branches,
            [
                Branch {
                    target: 4,
                    height: 1,
                    keep: 1
                },
                Branch {
                    target: 5,
                    height: 0,
                    keep: 1
                }
            ]
        );
        assert_eq!(
            f.instructions[3],
            Instruction::JumpTable { start: 0, len: 2 }
        );
    }

    #[test]
    fn unreachable_operands_do_not_inflate_runtime_stack_bounds() {
        let module = module(
            "(module (func (result i32)
            (block (result i32)
                i32.const 8 br 0
                (block i32.const 1 i32.const 2 drop drop)
                unreachable)
            i32.const 1 i32.add))",
        );
        assert_eq!(module.functions[0].max_stack, 2);
        let f = &module.functions[0];
        assert_eq!(
            f.instructions[1],
            Instruction::Jump(Branch {
                target: 7,
                height: 0,
                keep: 1
            })
        );
    }

    #[test]
    fn if_fixups_skip_the_other_arm_and_preserve_results() {
        let module = module(
            "(module (func (param i32) (result i64)
            local.get 0
            if (result i64) i64.const 11 else i64.const 22 end))",
        );
        let f = &module.functions[0];
        assert_eq!(f.instructions[1], Instruction::JumpIfZero(4));
        assert_eq!(
            f.instructions[3],
            Instruction::Jump(Branch {
                target: 5,
                height: 0,
                keep: 1
            })
        );
        assert_eq!(f.instructions[5], Instruction::Return);
    }

    #[test]
    fn floating_vector_lane_and_memory_immediates_preserve_bits() {
        let module = module(
            "(module (memory 1) (func
            f32.const -nan:0x412345 drop f64.const -0 drop
            v128.const i64x2 0x0123456789abcdef 0xfedcba9876543210
            i8x16.extract_lane_u 15 drop
            i32.const 0 v128.const i32x4 0 0 0 0
            v128.load8_lane offset=17 align=1 9 drop))",
        );
        let f = &module.functions[0];
        assert!(f.instructions.contains(&Instruction::Op {
            opcode: 0x43,
            a: 0,
            b: 0,
            bits: 0xffc12345
        }));
        assert!(f.instructions.contains(&Instruction::Op {
            opcode: 0x44,
            a: 0,
            b: 0,
            bits: 0x8000000000000000
        }));
        assert!(f.instructions.contains(&Instruction::Op {
            opcode: 0x20c,
            a: 0,
            b: 0,
            bits: 0xfedcba98765432100123456789abcdef
        }));
        assert!(f.instructions.contains(&Instruction::Op {
            opcode: 0x216,
            a: 15,
            b: 0,
            bits: 0
        }));
        assert!(f.instructions.contains(&Instruction::Op {
            opcode: 0x254,
            a: 17,
            b: 0,
            bits: 9
        }));
    }
}
