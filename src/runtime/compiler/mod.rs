//! Rewrites accepted operator callbacks into immutable slot bytecode.
//!
//! The streaming driver validates the complete input. Separate execution proofs
//! establish compiler normal return and source correspondence under allocator laws.
//!
//! Visitor callbacks report compiler budget exhaustion as
//! `VisitError::OutOfMemory` after recording the resource in `Budget`. They
//! report violated compiler invariants the same way without recording a
//! resource, and scheduler invariants as `Error::Host`.

use super::bytecode::{CompiledFunction, Instr, SimdImmediate};
use super::clear;
use super::platform::Alloc;
use super::value::{self, width};
use crate::{
    BlockType, CodeBatch, Config, Context, ElemType, Env, Error, LabelKind, MemArg, Module,
    ModuleVisitor, OpIterState, OpVisitor, Region, ResultType, Source, StackType, StreamingVisitor,
    Tail, ValidationProfile, ValueType, VisitError, VisitResult,
};
use alloc::vec::Vec;
use core::marker::PhantomData;

mod callbacks;
mod control;
mod initialize;
mod lower;
mod simd;

/// Bounds on the input and aggregate compiler artifacts for one module.
///
/// Defined-function and type caps bound input declarations. Instruction and
/// control counts include synthetic initialization code. The validator's
/// temporary metadata allocations retain its documented allocator-failure
/// limitation; compiler-owned storage uses fallible reserves.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
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
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
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
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub enum CompileError {
    Validation(Error),
    Resource(CompileResource),
}

#[cfg(not(charon))]
impl core::fmt::Display for CompileError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Validation(error) => error.fmt(f),
            Self::Resource(resource) => write!(f, "compiler resource exhausted: {resource:?}"),
        }
    }
}
#[cfg(all(feature = "std", not(charon)))]
impl std::error::Error for CompileError {}

struct Budget<A: Alloc> {
    marker: PhantomData<A>,
    limits: CompileLimits,
    instructions: usize,
    branches: usize,
    controls: usize,
    locals: usize,
    error: Option<CompileResource>,
}
impl<A: Alloc> Budget<A> {
    fn copy_state(&self) -> Self {
        Self {
            marker: PhantomData,
            limits: self.limits,
            instructions: self.instructions,
            branches: self.branches,
            controls: self.controls,
            locals: self.locals,
            error: self.error,
        }
    }
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
            _ => return Err(self.reject(resource)),
        };
        if *used >= limit {
            return Err(self.reject(resource));
        }
        *used += 1;
        Ok(())
    }
    fn push<T>(&mut self, values: &mut Vec<T>, value: T) -> VisitResult {
        if !A::reserve(values, 1) {
            return Err(self.reject(CompileResource::Allocation));
        }
        values.push(value);
        Ok(())
    }
}

/// Validated metadata and immutable executable code, independent of any instance.
///
/// Constructed only after the entire validation driver accepts, including its
/// tail and every issued worker. `lean/Itasca/Runtime` proves the rewriting and its
/// execution correct under explicit platform contracts.
#[cfg_attr(not(charon), derive(Debug))]
pub struct ExecutableModule {
    pub(super) module: Module,
    pub(super) profile: ValidationProfile,
    /// Defined functions, followed by compiled initialization code.
    pub(super) functions: Vec<CompiledFunction>,
    // The remaining fields are indices into `functions`.
    pub(super) global_initializers: Vec<usize>,
    pub(super) element_initializers: Vec<Vec<usize>>,
    pub(super) element_offsets: Vec<Option<usize>>,
    pub(super) data_offsets: Vec<Option<usize>>,
    pub(super) initialization: usize,
}

/// Sizes and original module byte coordinates of one defined function.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub struct FunctionStats {
    pub type_index: u32,
    /// Parameters and declared locals combined.
    pub local_count: usize,
    /// Maximum operand depth on a structurally reachable path.
    pub max_stack: usize,
    /// Total 64-bit slots reserved for locals and operands; vectors use two.
    pub slot_count: usize,
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
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
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
        self.module.env().func_type_indices().len()
    }
    /// Returns bounds for a defined-function index, excluding imports.
    pub fn function_stats(&self, index: usize) -> Option<FunctionStats> {
        if index >= self.function_count() {
            return None;
        }
        let f = match self.functions.get(index) {
            Some(function) => function,
            None => return None,
        };
        Some(FunctionStats {
            type_index: f.type_index,
            local_count: f.locals.len(),
            max_stack: f.max_stack,
            slot_count: f.slot_count as usize,
            instruction_count: f.code.len(),
            instruction_bytes: f.code.len() * const { core::mem::size_of::<Instr>() },
            branch_table_entries: f.jump_tables.len(),
            branch_table_bytes: f.jump_tables.len() * const { core::mem::size_of::<u32>() },
            body_start: f.body_start,
            body_end: f.body_end,
        })
    }
    /// Maps bytecode PCs to original opcode offsets in the complete module.
    ///
    /// `index` is a defined-function index, excluding imports. Eliminated
    /// structural operators are represented in `function_control_map`.
    pub fn function_source_offsets(&self, index: usize) -> Option<&[usize]> {
        if index >= self.function_count() {
            return None;
        }
        match self.functions.get(index) {
            Some(function) => Some(&function.source_offsets),
            None => None,
        }
    }
    /// Returns structured labels in opening order for a defined-function index.
    pub fn function_control_map(&self, index: usize) -> Option<&[ControlMap]> {
        if index >= self.function_count() {
            return None;
        }
        match self.functions.get(index) {
            Some(function) => Some(&function.controls),
            None => None,
        }
    }
}

/// Compiles with the default limits, reporting resource failures as
/// `Error::Visitor(VisitError::OutOfMemory)`.
pub(crate) fn compile_default_with<A: Alloc>(
    bytes: &[u8],
    profile: ValidationProfile,
) -> Result<ExecutableModule, Error> {
    match compile_with::<A>(bytes, profile, CompileLimits::default()) {
        Ok(module) => Ok(module),
        Err(CompileError::Validation(error)) => Err(error),
        Err(CompileError::Resource(_)) => Err(Error::Visitor(VisitError::OutOfMemory)),
    }
}

/// Validates and compiles a complete module with explicit budgets.
pub(crate) fn compile_with<A: Alloc>(
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
        func_param_slots: Vec::new(),
        completed: Vec::new(),
        functions: Vec::new(),
        tail: None,
        code_start,
        budget: Budget::<A> {
            marker: PhantomData,
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
    // Retain only owned compilation state before entering the collection loop.
    let CompileScheduler {
        mut budget,
        functions: mut pending_functions,
        tail,
        ..
    } = scheduler;
    let tail = tail.ok_or(CompileError::Validation(Error::Host))?;
    let functions = collect_functions(&mut budget, &mut pending_functions)?;
    let mut executable = ExecutableModule {
        module: Module { env, tail },
        profile,
        functions,
        global_initializers: Vec::new(),
        element_initializers: Vec::new(),
        element_offsets: Vec::new(),
        data_offsets: Vec::new(),
        initialization: 0,
    };
    if let Err(_) = initialize::lower(&mut executable, &mut budget) {
        return Err(CompileError::Resource(match budget.error {
            Some(resource) => resource,
            None => CompileResource::Allocation,
        }));
    }
    Ok(executable)
}

fn code_region(bytes: &[u8]) -> (usize, usize) {
    let mut pos = 8;
    let mut found = false;
    let mut bounds = (bytes.len(), bytes.len());
    while pos < bytes.len() && !found {
        let id = bytes[pos];
        if id > 10 && id != 12 {
            bounds = (pos, pos);
            found = true;
        } else {
            let end = match crate::reader::read_u32_leb(bytes, pos + 1) {
                Ok((len, contents)) => contents + (len as usize).min(bytes.len() - contents),
                Err(_) => bytes.len(),
            };
            if id == 10 {
                bounds = (pos, end);
                found = true;
            }
            pos = end;
        }
    }
    bounds
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

fn operand_at(before: &[u32], depth: usize) -> Result<u32, VisitError> {
    if depth == 0 {
        return Err(VisitError::OutOfMemory);
    }
    if depth > before.len() {
        return Err(VisitError::OutOfMemory);
    }
    Ok(before[before.len() - depth])
}

fn collect_functions<A: Alloc>(
    budget: &mut Budget<A>,
    pending: &mut Vec<Option<CompiledFunction>>,
) -> Result<Vec<CompiledFunction>, CompileError> {
    let mut functions = Vec::new();
    let mut index = 0;
    let mut result = Ok(());
    while index < pending.len() && result.is_ok() {
        result = take_function(budget, pending, index, &mut functions);
        index += 1;
    }
    result?;
    Ok(functions)
}

fn take_function<A: Alloc>(
    budget: &mut Budget<A>,
    pending: &mut Vec<Option<CompiledFunction>>,
    index: usize,
    functions: &mut Vec<CompiledFunction>,
) -> Result<(), CompileError> {
    let function = pending[index]
        .take()
        .ok_or(CompileError::Validation(Error::Host))?;
    match budget.push(functions, function) {
        Ok(()) => Ok(()),
        Err(_) => Err(CompileError::Resource(CompileResource::Allocation)),
    }
}

struct CompileScheduler<'a, A: Alloc> {
    signatures: Vec<Signature>,
    func_param_slots: Vec<u32>,
    completed: Vec<CodeBatch<'a>>,
    functions: Vec<Option<CompiledFunction>>,
    tail: Option<Tail>,
    code_start: usize,
    budget: Budget<A>,
}
impl<A: Alloc> ModuleVisitor for CompileScheduler<'_, A> {
    fn on_custom_section(&mut self, _section: crate::CustomSection) -> VisitResult {
        Ok(())
    }
}
impl<'a, A: Alloc> StreamingVisitor<'a> for CompileScheduler<'a, A> {
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
        let mut result = Ok(());
        while i < env.types().len() && result.is_ok() {
            result = self.capture_signature(env, i);
            i += 1;
        }
        result?;
        i = 0;
        while i < env.func_types().len() && result.is_ok() {
            result = self.capture_func_slots(env, i);
            i += 1;
        }
        result?;
        i = 0;
        while i < env.func_type_indices().len() && result.is_ok() {
            result = visitor_result(self.budget.push(&mut self.functions, None));
            i += 1;
        }
        result?;
        Ok(Config {
            batch_bytes: 25_000,
            max_batches: 4,
        })
    }
    fn submit_code_batch(&mut self, mut batch: CodeBatch<'a>) -> Result<(), Error> {
        let mut i = 0;
        let mut result = Ok(());
        while i < batch.len() && result.is_ok() {
            result = self.compile_entry(&mut batch);
            i += 1;
        }
        result?;
        visitor_result(self.budget.push(&mut self.completed, batch))?;
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
struct Signature {
    params: usize,
    results: usize,
    param_slots: u32,
    result_slots: u32,
}

fn visitor_result(result: VisitResult) -> Result<(), Error> {
    match result {
        Ok(()) => Ok(()),
        Err(error) => Err(Error::Visitor(error)),
    }
}

fn bounded_index(value: usize) -> Result<u32, VisitError> {
    if value > u32::MAX as usize {
        Err(VisitError::OutOfMemory)
    } else {
        Ok(value as u32)
    }
}

fn type_slots(types: &[ValueType]) -> Result<u32, Error> {
    let slots = value::type_slots(types).ok_or(Error::Host)?;
    if slots > u32::MAX as usize {
        Err(Error::Host)
    } else {
        Ok(slots as u32)
    }
}

/// Returns the slot width of an operand; unreachable-code operands use one slot.
fn stack_width(ty: StackType) -> u32 {
    match ty {
        StackType::Val(ty) => width(ty),
        StackType::Bot => 1,
    }
}

struct Frame {
    map: usize,
    kind: LabelKind,
    height: u32,
    params: u32,
    results: u32,
    start_pc: u32,
    if_pc: Option<usize>,
    entry_reachable: bool,
    end_reachable: bool,
    fixups: Vec<usize>,
}

struct FunctionCompiler<'a, A: Alloc> {
    signatures: &'a [Signature],
    func_param_slots: &'a [u32],
    budget: Budget<A>,
    batch_start: usize,
    function: CompiledFunction,
    frames: Vec<Frame>,
    reachable: bool,
    next_source: usize,
    before: Vec<u32>,
    height: u32,
    local_offsets: Vec<u32>,
    table_depths: Vec<u32>,
}

impl<'a, A: Alloc> FunctionCompiler<'a, A> {
    fn new(
        signatures: &'a [Signature],
        func_param_slots: &'a [u32],
        budget: Budget<A>,
        batch_start: usize,
    ) -> Self {
        Self {
            signatures,
            func_param_slots,
            budget,
            batch_start,
            function: CompiledFunction {
                locals: Vec::new(),
                local_slots: 0,
                param_slots: 0,
                slot_count: 0,
                max_stack: 0,
                code: Vec::new(),
                jump_tables: Vec::new(),
                v128_pool: Vec::new(),
                indirect: Vec::new(),
                simd: Vec::new(),
                source_offsets: Vec::new(),
                controls: Vec::new(),
                type_index: 0,
                body_start: 0,
                body_end: 0,
            },
            frames: Vec::new(),
            reachable: true,
            next_source: 0,
            before: Vec::new(),
            height: 0,
            local_offsets: Vec::new(),
            table_depths: Vec::new(),
        }
    }
    fn finish(self, validated: Result<(), Error>) -> (Result<CompiledFunction, Error>, Budget<A>) {
        if let Err(error) = validated {
            return (Err(error), self.budget);
        }
        if !self.frames.is_empty() || !self.function.well_formed() {
            return (Err(Error::Host), self.budget);
        }
        (Ok(self.function), self.budget)
    }
    fn pc(&mut self) -> Result<u32, VisitError> {
        if self.function.code.len() > u32::MAX as usize {
            Err(self.budget.reject(CompileResource::Instructions))
        } else {
            Ok(self.function.code.len() as u32)
        }
    }
    fn emit(&mut self, instruction: Instr) -> VisitResult {
        self.pc()?;
        self.budget.charge(CompileResource::Instructions)?;
        self.budget.push(&mut self.function.code, instruction)?;
        self.budget.push(
            &mut self.function.source_offsets,
            self.function.body_start + self.next_source,
        )
    }
    fn observe(&mut self, st: &OpIterState) -> VisitResult {
        if self.reachable {
            self.function.max_stack = self.function.max_stack.max(st.vals.len());
        }
        clear(&mut self.before);
        self.height = self.function.local_slots;
        observe_values(
            &mut self.budget,
            &mut self.before,
            &mut self.height,
            &st.vals,
        )?;
        if self.reachable {
            self.function.slot_count = self.function.slot_count.max(self.height);
        }
        self.next_source = st.pos;
        Ok(())
    }
    fn operand(&self, depth: usize) -> Result<u32, VisitError> {
        operand_at(&self.before, depth)
    }

    fn copy(&mut self, dst: u32, src: u32, n: u32) -> VisitResult {
        if n == 0 || src == dst {
            return Ok(());
        }
        let instruction = match n {
            1 => Instr::Copy { dst, src },
            2 => Instr::Copy2 { dst, src },
            _ => Instr::CopyN { dst, src, n },
        };
        self.emit(instruction)
    }
    fn pair(&mut self, a: u32, b: u32) -> Result<u32, VisitError> {
        let entry = bounded_index(self.function.indirect.len())?;
        self.budget.push(&mut self.function.indirect, (a, b))?;
        Ok(entry)
    }
    fn add_local(&mut self, ty: ValueType) -> VisitResult {
        self.budget.charge(CompileResource::Locals)?;
        self.budget
            .push(&mut self.local_offsets, self.function.local_slots)?;
        self.budget.push(&mut self.function.locals, ty)?;
        self.function.local_slots = self
            .function
            .local_slots
            .checked_add(width(ty))
            .ok_or(VisitError::OutOfMemory)?;
        Ok(())
    }
}

impl<'a, A: Alloc> CompileScheduler<'a, A> {
    fn capture_signature(&mut self, env: &Env, index: usize) -> Result<(), Error> {
        let signature = &env.types()[index];
        visitor_result(self.budget.push(
            &mut self.signatures,
            Signature {
                params: signature.params.len(),
                results: signature.results.len(),
                param_slots: type_slots(&signature.params)?,
                result_slots: type_slots(&signature.results)?,
            },
        ))
    }
    fn capture_func_slots(&mut self, env: &Env, index: usize) -> Result<(), Error> {
        visitor_result(self.budget.push(
            &mut self.func_param_slots,
            type_slots(&env.func_types()[index].params)?,
        ))
    }
    fn compile_entry(&mut self, batch: &mut CodeBatch<'a>) -> Result<(), Error> {
        let entry = batch.next_entry()?;
        let mut compiler = FunctionCompiler::new(
            &self.signatures,
            &self.func_param_slots,
            self.budget.copy_state(),
            self.code_start + batch.code_offset(),
        );
        let validated = batch.validate_func(entry.index, &mut compiler);
        let (function, budget) = compiler.finish(validated);
        self.budget = budget;
        let function = function?;
        if entry.index >= self.functions.len() || self.functions[entry.index].is_some() {
            return Err(Error::Host);
        }
        self.functions[entry.index] = Some(function);
        Ok(())
    }
}

fn observe_value<A: Alloc>(
    budget: &mut Budget<A>,
    before: &mut Vec<u32>,
    height: &mut u32,
    ty: StackType,
) -> VisitResult {
    budget.push(before, *height)?;
    *height = height
        .checked_add(stack_width(ty))
        .ok_or(VisitError::OutOfMemory)?;
    Ok(())
}

fn observe_values<A: Alloc>(
    budget: &mut Budget<A>,
    before: &mut Vec<u32>,
    height: &mut u32,
    values: &[StackType],
) -> VisitResult {
    let mut i = 0;
    let mut result = Ok(());
    while i < values.len() && result.is_ok() {
        result = observe_value(budget, before, height, values[i]);
        i += 1;
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    fn compile_wat(source: &str) -> ExecutableModule {
        let buffer = wast::parser::ParseBuffer::new(source).unwrap();
        let bytes = wast::parser::parse::<wast::Wat>(&buffer)
            .unwrap()
            .encode()
            .unwrap();
        crate::runtime::compile(&bytes, ValidationProfile::Wasm2).unwrap()
    }

    #[test]
    fn bytecode_stays_sixteen_bytes() {
        assert_eq!(const { core::mem::size_of::<Instr>() }, 16);
    }

    #[test]
    fn mixed_width_control_and_calls_compile() {
        let module = compile_wat(
            "(module
            (func $id (param v128 i64) (result v128 i64) local.get 0 local.get 1)
            (func (param i32) (result v128 i64)
                (block (result v128 i64)
                    v128.const i32x4 1 2 3 4 i64.const 9
                    (loop (param v128 i64) (result v128 i64)
                        local.get 0 br_if 0
                        call $id br 1))))",
        );
        assert!(module.functions[0].well_formed());
        assert!(module.functions[1].well_formed());
        assert_eq!(module.functions[0].local_slots, 3);
        assert_eq!(module.functions[0].param_slots, 3);
    }

    #[test]
    fn dead_polymorphic_code_needs_no_operand_storage() {
        let module = compile_wat("(module (func (result v128) unreachable))");
        assert_eq!(module.functions[0].slot_count, 0);
        assert!(module.functions[0].well_formed());
    }

    #[test]
    fn initialization_is_compiled_without_exposing_extra_functions() {
        let module = compile_wat(
            "(module (memory 1) (table 1 funcref)
            (func $f) (global v128 (v128.const i32x4 1 2 3 4))
            (elem (i32.const 0) func $f) (data (i32.const 0) \"abc\"))",
        );
        assert_eq!(module.function_count(), 1);
        assert!(module.function_stats(1).is_none());
        assert!(module.function_source_offsets(1).is_none());
        assert!(module.function_control_map(1).is_none());
        assert!(module.functions.len() > module.function_count());
        let mut i = 0;
        while i < module.functions.len() {
            assert!(module.functions[i].well_formed());
            i += 1;
        }
    }

    #[test]
    fn table_stubs_and_nested_dead_blocks_compile() {
        let module = compile_wat(
            "(module (func (param i32) (result i32)
            (block (result i32)
                i64.const 9
                (block (result i32) i32.const 7 local.get 0 br_table 0 1)
                return)))",
        );
        assert_eq!(module.functions[0].jump_tables.len(), 2);
        let module = compile_wat(
            "(module (func (result i32)
            (block (result i32) i32.const 8 br 0
                (block i32.const 1 i32.const 2 drop drop) unreachable)
            i32.const 1 i32.add))",
        );
        assert_eq!(module.functions[0].max_stack, 2);
    }
}
