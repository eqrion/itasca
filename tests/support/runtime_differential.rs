//! Shared, bounded differential execution against pinned Wasmi 2.0.0.
//!
//! Callers must supply deterministic numeric modules (wasm-smith's per-operation
//! NaN canonicalization or finite focused workloads), not merely normalize final
//! NaN results. The returned coverage distinguishes limits from equivalence.
#![allow(dead_code)]

use itasca::runtime::{
    self as rt, ExecError, Execution, Extern, Instantiated, MemoryBuffer, Store, Trap, Value,
};
use itasca::{ElemType, ImportDesc, Mut, ValidationProfile, ValueType};
use wasmi::{Nullable, Val};

const INTERRUPTS: u64 = 5_000_000;
const MEMORY_LIMIT: usize = 16 * 65536;
const TABLE_LIMIT: usize = 4096;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Coverage {
    Compared,
    Invalid,
    ResourceLimit,
    ProfileDifference,
    UnsupportedReference,
    NumericNondeterminism,
}

/// Records semantic comparisons and exclusions separately during fuzz campaigns.
pub fn record(status: Coverage) {
    use std::sync::atomic::{AtomicU64, Ordering};
    static COUNTS: [AtomicU64; 6] = [const { AtomicU64::new(0) }; 6];
    static TOTAL: AtomicU64 = AtomicU64::new(0);
    COUNTS[status as usize].fetch_add(1, Ordering::Relaxed);
    let total = TOTAL.fetch_add(1, Ordering::Relaxed) + 1;
    if total == 1 || total % 1024 == 0 || std::env::var_os("ITASCA_FUZZ_REPORT_EACH").is_some() {
        let counts: Vec<_> = COUNTS.iter().map(|c| c.load(Ordering::Relaxed)).collect();
        eprintln!("execution coverage total={total} [compared,invalid,resource,profile,reference,numeric]={counts:?}");
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Symbol {
    I32(u32),
    I64(u64),
    F32(u32),
    F64(u64),
    V128(u128),
    Func(Option<usize>),
    Extern(Option<u64>),
}

#[derive(Debug, PartialEq, Eq)]
enum ResultKind {
    Returned,
    Trap(Trap),
    Link,
    Resource,
}

struct HostState {
    trace: Vec<(u64, Vec<Symbol>)>,
    functions: Vec<wasmi::Func>,
    limits: wasmi::StoreLimits,
    unknown_reference: bool,
}

pub struct Pair {
    ours: Store,
    oracle: wasmi::Store<HostState>,
    engine: wasmi::Engine,
    functions: Vec<rt::FuncAddr>,
    trace: Vec<(u64, Vec<Symbol>)>,
    objects: Vec<(Extern, wasmi::Extern)>,
    instances: Vec<(rt::InstanceAddr, wasmi::Instance)>,
}

struct TracePlatform<'a> {
    remaining: u64,
    functions: &'a [rt::FuncAddr],
    trace: &'a mut Vec<(u64, Vec<Symbol>)>,
    unsupported: bool,
}
impl rt::Platform<rt::VecMemory> for TracePlatform<'_> {
    fn interrupt(&mut self) -> rt::InterruptAction {
        if self.remaining == 0 {
            rt::InterruptAction::Terminate
        } else {
            self.remaining -= 1;
            rt::InterruptAction::Continue
        }
    }
    fn call_host(
        &mut self,
        store: &mut Store,
        id: u64,
        args: &[Value],
        _: &mut [Value],
    ) -> Result<(), rt::HostError> {
        let args: Option<Vec<_>> = args
            .iter()
            .map(|v| {
                Some(match *v {
                    Value::I32(x) => Symbol::I32(x),
                    Value::I64(x) => Symbol::I64(x),
                    Value::F32(x) => Symbol::F32(x),
                    Value::F64(x) => Symbol::F64(x),
                    Value::V128(x) => Symbol::V128(x),
                    Value::FuncRef(None) => Symbol::Func(None),
                    Value::FuncRef(Some(f)) => {
                        Symbol::Func(Some(self.functions.iter().position(|x| *x == f)?))
                    }
                    Value::ExternRef(None) => Symbol::Extern(None),
                    Value::ExternRef(Some(r)) => {
                        Symbol::Extern(Some(store.extern_identity(r).unwrap()))
                    }
                })
            })
            .collect();
        match args {
            Some(args) => {
                self.trace.push((id, args));
                Ok(())
            }
            None => {
                self.unsupported = true;
                Err(rt::HostError::Trap)
            }
        }
    }
}

fn oracle_type(ty: ValueType) -> wasmi::ValType {
    match ty {
        ValueType::I32 => wasmi::ValType::I32,
        ValueType::I64 => wasmi::ValType::I64,
        ValueType::F32 => wasmi::ValType::F32,
        ValueType::F64 => wasmi::ValType::F64,
        ValueType::V128 => wasmi::ValType::V128,
        ValueType::FuncRef => wasmi::ValType::FuncRef,
        ValueType::ExternRef => wasmi::ValType::ExternRef,
    }
}

fn oracle_external_type(ty: &itasca::ExternType) -> wasmi::ExternType {
    match ty {
        itasca::ExternType::Func(t) => wasmi::ExternType::Func(wasmi::FuncType::new(
            t.params.iter().copied().map(oracle_type),
            t.results.iter().copied().map(oracle_type),
        )),
        itasca::ExternType::Memory(t) => {
            wasmi::ExternType::Memory(wasmi::MemoryType::new(t.limits.min, t.limits.max))
        }
        itasca::ExternType::Table(t) => wasmi::ExternType::Table(wasmi::TableType::new(
            if t.elem == ElemType::FuncRef {
                wasmi::RefType::Func
            } else {
                wasmi::RefType::Extern
            },
            t.limits.min,
            t.limits.max,
        )),
        itasca::ExternType::Global(t) => wasmi::ExternType::Global(wasmi::GlobalType::new(
            oracle_type(t.valtype),
            if t.mutability == Mut::Var {
                wasmi::Mutability::Var
            } else {
                wasmi::Mutability::Const
            },
        )),
    }
}

fn same_external_type(a: &wasmi::ExternType, b: &wasmi::ExternType) -> bool {
    match (a, b) {
        (wasmi::ExternType::Func(a), wasmi::ExternType::Func(b)) => a == b,
        (wasmi::ExternType::Global(a), wasmi::ExternType::Global(b)) => a == b,
        (wasmi::ExternType::Memory(a), wasmi::ExternType::Memory(b)) => a == b,
        (wasmi::ExternType::Table(a), wasmi::ExternType::Table(b)) => a == b,
        _ => false,
    }
}

fn zero(ty: ValueType) -> Value {
    match ty {
        ValueType::I32 => Value::I32(0),
        ValueType::I64 => Value::I64(0),
        ValueType::F32 => Value::F32(0),
        ValueType::F64 => Value::F64(0),
        ValueType::V128 => Value::V128(0),
        ValueType::FuncRef => Value::FuncRef(None),
        ValueType::ExternRef => Value::ExternRef(None),
    }
}

fn oracle_value(value: Value) -> Val {
    match value {
        Value::I32(x) => Val::I32(x as i32),
        Value::I64(x) => Val::I64(x as i64),
        Value::F32(x) => Val::F32(wasmi::F32::from_bits(x)),
        Value::F64(x) => Val::F64(wasmi::F64::from_bits(x)),
        Value::V128(x) => Val::V128(x.into()),
        Value::FuncRef(None) => Val::FuncRef(Nullable::Null),
        Value::ExternRef(None) => Val::ExternRef(Nullable::Null),
        _ => unreachable!("argument references are null"),
    }
}

fn oracle_symbol(
    value: &Val,
    state: &HostState,
    context: impl wasmi::AsContext<Data = HostState>,
) -> Option<Symbol> {
    Some(match value {
        Val::I32(x) => Symbol::I32(*x as u32),
        Val::I64(x) => Symbol::I64(*x as u64),
        Val::F32(x) => Symbol::F32(x.to_bits()),
        Val::F64(x) => Symbol::F64(x.to_bits()),
        Val::V128(x) => Symbol::V128(x.as_u128()),
        Val::FuncRef(Nullable::Null) => Symbol::Func(None),
        Val::ExternRef(Nullable::Null) => Symbol::Extern(None),
        Val::FuncRef(Nullable::Val(x)) => Symbol::Func(Some(
            state
                .functions
                .iter()
                .position(|f| oracle_function_key(*f) == oracle_function_key(*x))?,
        )),
        Val::ExternRef(Nullable::Val(x)) => {
            Symbol::Extern(Some(*x.data(context.as_context()).downcast_ref::<u64>()?))
        }
    })
}

// Wasmi 2.0.0 exposes no public Func equality operation. Its pinned Debug
// representation includes the store and function keys. Use that only within
// the oracle to look up the shared symbolic ID; never compare private engine
// addresses across runtimes. A dependency update must recheck this adapter.
fn oracle_function_key(function: wasmi::Func) -> String {
    format!("{function:?}")
}

fn oracle_error(error: wasmi::Error) -> ResultKind {
    use wasmi::TrapCode as T;
    if let wasmi::errors::ErrorKind::Instantiation(reason) = error.kind() {
        use wasmi::errors::InstantiationError as E;
        return match reason {
            E::ImportTypeMismatch { .. }
            | E::GlobalTypeMismatch { .. }
            | E::FuncTypeMismatch { .. }
            | E::TableTypeMismatch { .. }
            | E::MemoryTypeMismatch { .. }
            | E::MismatchedNumberOfImports { .. } => ResultKind::Link,
            E::ElementSegmentDoesNotFit { .. } => ResultKind::Trap(Trap::TableOutOfBounds),
            E::TooManyInstances
            | E::TooManyTables
            | E::TooManyMemories
            | E::FailedToInstantiateMemory(_)
            | E::FailedToInstantiateTable(_) => ResultKind::Resource,
            _ => panic!("unexpected oracle instantiation error: {error:?}"),
        };
    }
    let trap = match error.as_trap_code() {
        Some(T::UnreachableCodeReached) => Trap::Unreachable,
        Some(T::MemoryOutOfBounds) => Trap::MemoryOutOfBounds,
        Some(T::TableOutOfBounds) => Trap::TableOutOfBounds,
        Some(T::IndirectCallToNull) => Trap::UninitializedElement,
        Some(T::IntegerDivisionByZero) => Trap::IntegerDivideByZero,
        Some(T::IntegerOverflow) => Trap::IntegerOverflow,
        Some(T::BadConversionToInteger) => Trap::InvalidConversionToInteger,
        Some(T::BadSignature) => Trap::IndirectCallTypeMismatch,
        Some(
            T::StackOverflow | T::OutOfFuel | T::GrowthOperationLimited | T::OutOfSystemMemory,
        ) => return ResultKind::Resource,
        None => panic!("unexpected oracle error: {error:?}"),
    };
    ResultKind::Trap(trap)
}

fn our_error(error: ExecError) -> ResultKind {
    match error {
        ExecError::Trap(trap) => ResultKind::Trap(trap),
        ExecError::Link(_) => ResultKind::Link,
        ExecError::Exhausted(_) | ExecError::Terminated => ResultKind::Resource,
        other => panic!("unexpected itasca runtime failure: {other:?}"),
    }
}

impl Pair {
    pub fn new(profile: ValidationProfile) -> Self {
        let wasm2 = profile == ValidationProfile::Wasm2;
        let mut config = wasmi::Config::default();
        config
            .wasm_mutable_global(true)
            .wasm_sign_extension(wasm2)
            .wasm_saturating_float_to_int(wasm2)
            .wasm_multi_value(wasm2)
            .wasm_bulk_memory(wasm2)
            .wasm_reference_types(wasm2)
            .wasm_simd(wasm2)
            .wasm_multi_memory(false)
            .wasm_tail_call(false)
            .wasm_extended_const(false)
            .wasm_custom_page_sizes(false)
            .wasm_wide_arithmetic(false)
            .wasm_relaxed_simd(false);
        let engine = wasmi::Engine::new(&config);
        let state = HostState {
            trace: vec![],
            functions: vec![],
            unknown_reference: false,
            limits: wasmi::StoreLimitsBuilder::new()
                .memory_size(MEMORY_LIMIT)
                .table_elements(TABLE_LIMIT)
                .build(),
        };
        let mut oracle = wasmi::Store::new(&engine, state);
        oracle.limiter(|s| &mut s.limits);
        let ours = Store::with_limits(rt::StoreLimits {
            max_memory_bytes: MEMORY_LIMIT,
            max_table_elements: TABLE_LIMIT * 8,
            max_frames: 512,
            max_values: 100_000,
            ..rt::StoreLimits::default()
        });
        Self {
            ours,
            oracle,
            engine,
            functions: vec![],
            trace: vec![],
            objects: vec![],
            instances: vec![],
        }
    }

    fn symbol(&self, value: Value) -> Option<Symbol> {
        Some(match value {
            Value::I32(x) => Symbol::I32(x),
            Value::I64(x) => Symbol::I64(x),
            Value::F32(x) => Symbol::F32(x),
            Value::F64(x) => Symbol::F64(x),
            Value::V128(x) => Symbol::V128(x),
            Value::FuncRef(None) => Symbol::Func(None),
            Value::ExternRef(None) => Symbol::Extern(None),
            Value::FuncRef(Some(x)) => {
                Symbol::Func(Some(self.functions.iter().position(|f| *f == x)?))
            }
            Value::ExternRef(Some(x)) => {
                Symbol::Extern(Some(self.ours.extern_identity(x).unwrap()))
            }
        })
    }

    fn register_object(&mut self, ours: Extern, oracle: wasmi::Extern) {
        if let (Extern::Func(a), wasmi::Extern::Func(b)) = (ours, oracle) {
            if let Some(index) = self.functions.iter().position(|f| *f == a) {
                assert_eq!(
                    oracle_function_key(self.oracle.data().functions[index]),
                    oracle_function_key(b),
                    "function aliases differ"
                );
            } else {
                self.functions.push(a);
                self.oracle.data_mut().functions.push(b);
            }
        }
        self.objects.push((ours, oracle));
    }

    fn observe(&self) -> Coverage {
        if self.oracle.data().unknown_reference {
            return Coverage::UnsupportedReference;
        }
        assert_eq!(
            self.trace,
            self.oracle.data().trace,
            "host call order or arguments differ"
        );
        for (ours, oracle) in &self.objects {
            match (ours, oracle) {
                (Extern::Memory(a), wasmi::Extern::Memory(b)) => assert_eq!(
                    self.ours.memory(*a).unwrap(),
                    b.data(&self.oracle),
                    "memory effects differ"
                ),
                (Extern::Global(a), wasmi::Extern::Global(b)) => {
                    let Some(a) = self.symbol(self.ours.global(*a).unwrap()) else {
                        return Coverage::UnsupportedReference;
                    };
                    let Some(b) =
                        oracle_symbol(&b.get(&self.oracle), self.oracle.data(), &self.oracle)
                    else {
                        return Coverage::UnsupportedReference;
                    };
                    assert_eq!(a, b, "global effects differ");
                }
                (Extern::Table(a), wasmi::Extern::Table(b)) => {
                    let values: Vec<_> = (0..self.ours.table_size(*a).unwrap())
                        .map(|i| self.ours.table_get(*a, i).unwrap())
                        .collect();
                    assert_eq!(
                        values.len() as u64,
                        b.size(&self.oracle),
                        "table growth differs"
                    );
                    for (i, value) in values.iter().enumerate() {
                        let Some(a) = self.symbol(*value) else {
                            return Coverage::UnsupportedReference;
                        };
                        let Some(b) = oracle_symbol(
                            &b.get(&self.oracle, i as u64).unwrap().into(),
                            self.oracle.data(),
                            &self.oracle,
                        ) else {
                            return Coverage::UnsupportedReference;
                        };
                        assert_eq!(a, b, "table element {i} differs");
                    }
                }
                (Extern::Func(_), wasmi::Extern::Func(_)) => {}
                _ => panic!("export kind differs"),
            }
        }
        Coverage::Compared
    }

    /// Instantiates a module, optionally resolving imports from an earlier module.
    pub fn instantiate(
        &mut self,
        bytes: &[u8],
        profile: ValidationProfile,
        provider: Option<usize>,
    ) -> Coverage {
        let normalized;
        let input = if profile == ValidationProfile::Wasm1 {
            normalized = match crate::mvp_binary::normalize_to_wasm1(bytes) {
                Ok(bytes) => bytes,
                Err(_) => return Coverage::Invalid,
            };
            &normalized
        } else {
            bytes
        };
        let module = match rt::compile(input, profile) {
            Ok(module) => module,
            Err(_) => return Coverage::Invalid,
        };
        let oracle_module = wasmi::Module::new(&self.engine, bytes)
            .expect("oracle rejected accepted profile module");
        let mut our_imports = Vec::new();
        let mut oracle_imports = Vec::new();
        for (id, import) in module.env().imports().iter().enumerate() {
            let pair = if let Some(provider) = provider {
                let (a, b) = self.instances[provider];
                (
                    self.ours
                        .export(a, &import.name)
                        .unwrap()
                        .expect("provider export"),
                    b.get_export(&self.oracle, std::str::from_utf8(&import.name).unwrap())
                        .expect("oracle provider export"),
                )
            } else {
                match import.desc {
                    ImportDesc::Func(index) => {
                        let ty = module.env().types()[index as usize].clone();
                        let oracle_ty = wasmi::FuncType::new(
                            ty.params.iter().copied().map(oracle_type),
                            ty.results.iter().copied().map(oracle_type),
                        );
                        let result_types = oracle_ty.results().to_vec();
                        let a = self.ours.define_host(ty, id as u64).unwrap();
                        let b = wasmi::Func::new(
                            &mut self.oracle,
                            oracle_ty,
                            move |mut caller, arguments, results| {
                                let args = arguments
                                    .iter()
                                    .map(|v| oracle_symbol(v, caller.data(), &caller))
                                    .collect::<Option<Vec<_>>>();
                                if let Some(args) = args {
                                    caller.data_mut().trace.push((id as u64, args));
                                } else {
                                    caller.data_mut().unknown_reference = true;
                                }
                                for (result, ty) in results.iter_mut().zip(&result_types) {
                                    *result = Val::default_for_ty(*ty);
                                }
                                Ok(())
                            },
                        );
                        (Extern::Func(a), wasmi::Extern::Func(b))
                    }
                    ImportDesc::Memory(ty) => {
                        if ty.limits.min as usize > MEMORY_LIMIT / 65536 {
                            return Coverage::ResourceLimit;
                        }
                        let a = self
                            .ours
                            .define_memory(
                                ty,
                                rt::VecMemory::new_zeroed(ty.limits.min as usize * 65536).unwrap(),
                            )
                            .unwrap();
                        let b = wasmi::Memory::new(
                            &mut self.oracle,
                            wasmi::MemoryType::new(ty.limits.min, ty.limits.max),
                        )
                        .unwrap();
                        (Extern::Memory(a), wasmi::Extern::Memory(b))
                    }
                    ImportDesc::Table(ty) => {
                        if ty.limits.min as usize > TABLE_LIMIT {
                            return Coverage::ResourceLimit;
                        }
                        let elem = if ty.elem == ElemType::FuncRef {
                            wasmi::RefType::Func
                        } else {
                            wasmi::RefType::Extern
                        };
                        let a = self.ours.define_table(ty).unwrap();
                        let b = wasmi::Table::new(
                            &mut self.oracle,
                            wasmi::TableType::new(elem, ty.limits.min, ty.limits.max),
                            wasmi::Ref::null(elem),
                        )
                        .unwrap();
                        (Extern::Table(a), wasmi::Extern::Table(b))
                    }
                    ImportDesc::Global(ty) => {
                        let value = zero(ty.valtype);
                        let a = self.ours.define_global(ty, value).unwrap();
                        let b = wasmi::Global::new(
                            &mut self.oracle,
                            oracle_value(value),
                            if ty.mutability == Mut::Var {
                                wasmi::Mutability::Var
                            } else {
                                wasmi::Mutability::Const
                            },
                        );
                        (Extern::Global(a), wasmi::Extern::Global(b))
                    }
                }
            };
            self.register_object(pair.0, pair.1);
            our_imports.push(pair.0);
            oracle_imports.push(pair.1);
        }
        if module
            .env()
            .mem_types()
            .iter()
            .any(|m| m.limits.min as usize > MEMORY_LIMIT / 65536)
            || module
                .env()
                .table_types()
                .iter()
                .any(|t| t.limits.min as usize > TABLE_LIMIT)
        {
            return Coverage::ResourceLimit;
        }
        // The oracle's module iterator is authoritative for its import order.
        // Match names explicitly instead of relying on internal index grouping.
        let mut used = vec![false; oracle_imports.len()];
        let expected_imports = itasca::import_types(module.env()).unwrap();
        let oracle_imports: Vec<_> = oracle_module
            .imports()
            .map(|required| {
                let index = module
                    .env()
                    .imports()
                    .iter()
                    .enumerate()
                    .position(|(i, candidate)| {
                        !used[i]
                            && candidate.module == required.module().as_bytes()
                            && candidate.name == required.name().as_bytes()
                            && same_external_type(
                                &oracle_external_type(&expected_imports[i]),
                                required.ty(),
                            )
                    })
                    .unwrap();
                used[index] = true;
                oracle_imports[index]
            })
            .collect();
        let export_names: Vec<_> = module
            .env()
            .exports()
            .iter()
            .map(|e| e.name.clone())
            .collect();
        let mut platform = TracePlatform {
            remaining: INTERRUPTS,
            functions: &self.functions,
            trace: &mut self.trace,
            unsupported: false,
        };
        let ours = match self.ours.instantiate(module, &our_imports, &mut platform) {
            Ok(Instantiated {
                instance,
                start: Some(start),
            }) => Execution::new()
                .invoke(&mut self.ours, &mut platform, start, &[], &mut Vec::new())
                .map(|()| instance),
            Ok(instantiated) => Ok(instantiated.instance),
            Err(error) => Err(error),
        };
        if platform.unsupported {
            return Coverage::UnsupportedReference;
        }
        let (our_instance, our_result) = match ours {
            Ok(instance) => (Some(instance), ResultKind::Returned),
            Err(error) => (None, our_error(error)),
        };
        if our_result == ResultKind::Resource {
            return Coverage::ResourceLimit;
        }
        let oracle_result = wasmi::Instance::new(&mut self.oracle, &oracle_module, &oracle_imports);
        let (oracle_instance, oracle_result) = match oracle_result {
            Ok(instance) => (Some(instance), ResultKind::Returned),
            Err(error) => {
                if our_result == ResultKind::Returned {
                    eprintln!("oracle instantiation error: {error:?}");
                }
                (None, oracle_error(error))
            }
        };
        if our_result == ResultKind::Resource || oracle_result == ResultKind::Resource {
            return Coverage::ResourceLimit;
        }
        assert_eq!(our_result, oracle_result, "instantiation outcomes differ");
        if let (Some(a), Some(b)) = (our_instance, oracle_instance) {
            self.instances.push((a, b));
            for name in &export_names {
                let a = self.ours.export(a, name).unwrap().unwrap();
                let b = b
                    .get_export(&self.oracle, std::str::from_utf8(name).unwrap())
                    .unwrap();
                self.register_object(a, b);
            }
        } else if profile == ValidationProfile::Wasm1
            && matches!(
                our_result,
                ResultKind::Trap(Trap::MemoryOutOfBounds | Trap::TableOutOfBounds)
            )
        {
            // Wasmi uses current sequential segment writes even with proposal
            // features disabled. Wasm 1's historical precheck is covered by WAST.
            return Coverage::ProfileDifference;
        }
        self.observe()
    }

    pub fn call(&mut self, instance: usize, name: &str, arguments: &[Value]) -> Coverage {
        let (a, b) = self.instances[instance];
        let Some(Extern::Func(function)) = self.ours.export(a, name.as_bytes()).unwrap() else {
            panic!("function export missing")
        };
        let oracle_function = b.get_func(&self.oracle, name).unwrap();
        let oracle_arguments: Vec<_> = arguments.iter().copied().map(oracle_value).collect();
        let mut oracle_values: Vec<_> = oracle_function
            .ty(&self.oracle)
            .results()
            .iter()
            .copied()
            .map(Val::default_for_ty)
            .collect();
        let mut values = Vec::new();
        let mut platform = TracePlatform {
            remaining: INTERRUPTS,
            functions: &self.functions,
            trace: &mut self.trace,
            unsupported: false,
        };
        let ours = rt::Execution::new()
            .invoke(
                &mut self.ours,
                &mut platform,
                function,
                arguments,
                &mut values,
            )
            .map_or_else(our_error, |_| ResultKind::Returned);
        if platform.unsupported {
            return Coverage::UnsupportedReference;
        }
        if ours == ResultKind::Resource {
            return Coverage::ResourceLimit;
        }
        let oracle_result = oracle_function
            .call(&mut self.oracle, &oracle_arguments, &mut oracle_values)
            .map_or_else(oracle_error, |_| ResultKind::Returned);
        if ours == ResultKind::Resource || oracle_result == ResultKind::Resource {
            return Coverage::ResourceLimit;
        }
        assert_eq!(
            ours, oracle_result,
            "call {name:?} outcomes differ; arguments={arguments:?}"
        );
        if ours == ResultKind::Returned {
            let Some(values) = values
                .into_iter()
                .map(|v| self.symbol(v))
                .collect::<Option<Vec<_>>>()
            else {
                return Coverage::UnsupportedReference;
            };
            let Some(expected) = oracle_values
                .iter()
                .map(|v| oracle_symbol(v, self.oracle.data(), &self.oracle))
                .collect::<Option<Vec<_>>>()
            else {
                return Coverage::UnsupportedReference;
            };
            assert_eq!(
                values, expected,
                "call {name:?} results differ; arguments={arguments:?}"
            );
        }
        self.observe()
    }
}

/// Compare bounded instantiation and three rounds of calls to every export.
pub fn compare(bytes: &[u8], profile: ValidationProfile, argument_seed: &[u8]) -> Coverage {
    let mut pair = Pair::new(profile);
    let status = pair.instantiate(bytes, profile, None);
    if status != Coverage::Compared || pair.instances.is_empty() {
        return status;
    }
    let exports: Vec<_> = pair.instances[0]
        .1
        .exports(&pair.oracle)
        .filter_map(|e| e.into_extern().into_func().map(|f| f))
        .collect();
    // Get names separately because Export::into_extern consumes its wrapper.
    let names: Vec<_> = pair.instances[0]
        .1
        .exports(&pair.oracle)
        .filter(|e| matches!(e.ty(&pair.oracle), wasmi::ExternType::Func(_)))
        .map(|e| e.name().to_owned())
        .collect();
    let mut offset = 0;
    for _ in 0..3 {
        for (name, function) in names.iter().zip(&exports) {
            let ty = function.ty(&pair.oracle);
            let args = ty
                .params()
                .iter()
                .map(|ty| {
                    let mut bits = 0u64;
                    for i in 0..8 {
                        bits |= (argument_seed
                            .get(offset % argument_seed.len().max(1))
                            .copied()
                            .unwrap_or(0) as u64)
                            << (i * 8);
                        offset += 1;
                    }
                    match ty {
                        wasmi::ValType::I32 => Value::I32(bits as u32),
                        wasmi::ValType::I64 => Value::I64(bits),
                        // Finite arguments avoid NaN inputs in strict comparisons.
                        wasmi::ValType::F32 => Value::F32(((bits as i32) as f32).to_bits()),
                        wasmi::ValType::F64 => Value::F64(((bits as i64) as f64).to_bits()),
                        wasmi::ValType::V128 => {
                            Value::V128((bits as u128) | ((bits as u128) << 64))
                        }
                        wasmi::ValType::FuncRef => Value::FuncRef(None),
                        wasmi::ValType::ExternRef => Value::ExternRef(None),
                    }
                })
                .collect::<Vec<_>>();
            let status = pair.call(0, name, &args);
            if status != Coverage::Compared {
                return status;
            }
        }
    }
    Coverage::Compared
}
