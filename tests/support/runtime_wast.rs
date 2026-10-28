use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use itasca::runtime::{
    compile, ExecError, ExecutableModule, Execution, Extern, ExternAddr, HostError, InstanceAddr,
    InterruptAction, LinkError, MemoryBuffer, Platform, ResourceLimit, Store, StoreLimits, Trap,
    Value, VecMemory,
};
use itasca::{
    ElemType, FuncType, GlobalType, Limits, MemType, Mut, TableType, ValidationProfile, ValueType,
};
use wast::core::{
    AbstractHeapType, DataKind, ElemKind, HeapType, ModuleField, ModuleKind, NanPattern,
    V128Pattern, WastArgCore, WastRetCore,
};
use wast::{QuoteWat, Wast, WastArg, WastDirective, WastExecute, WastInvoke, WastRet, Wat};

// These harness limits are infrastructure failures, never Wasm traps or exhaustion.
const ACTION_INTERRUPTS: u64 = 1_000_000_000;
const MAX_HOST_CALLS: usize = 1_000_000;

struct SpectestPlatform {
    remaining: u64,
    calls: usize,
    failure: Option<&'static str>,
}
impl SpectestPlatform {
    fn new() -> Self {
        Self {
            remaining: ACTION_INTERRUPTS,
            calls: 0,
            failure: None,
        }
    }
    fn check(&self) -> Result<()> {
        self.failure
            .map_or(Ok(()), |why| Err(Failure::Infrastructure(why)))
    }
}
impl Platform<VecMemory> for SpectestPlatform {
    fn interrupt(&mut self) -> InterruptAction {
        if self.remaining == 0 {
            self.failure = Some("interrupt limit");
            InterruptAction::Terminate
        } else {
            self.remaining -= 1;
            InterruptAction::Continue
        }
    }
    fn call_host(
        &mut self,
        _: &mut Store,
        id: u64,
        _: &[Value],
        results: &mut [Value],
    ) -> std::result::Result<(), HostError> {
        self.calls += 1;
        if self.calls > MAX_HOST_CALLS {
            self.failure = Some("host call limit");
        } else if id >= 7 {
            self.failure = Some("unknown spectest host identifier");
        } else if !results.is_empty() {
            self.failure = Some("spectest print returned values");
        }
        if self.failure.is_some() {
            Err(HostError::Trap)
        } else {
            Ok(())
        }
    }
}

#[derive(Debug, Default, PartialEq, Eq)]
struct Counts {
    files: usize,
    modules: usize,
    malformed_text: usize,
    malformed_binary: usize,
    invalid: usize,
    registrations: usize,
    invocations: usize,
    returns: usize,
    traps: usize,
    unlinkable: usize,
    exhaustion: usize,
    legacy_nan: usize,
    unsupported: usize,
}

enum Failure {
    Encoding(String),
    Validation(itasca::Error),
    Runtime(ExecError),
    Infrastructure(&'static str),
    Script(String),
}

impl std::fmt::Debug for Failure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Encoding(e) => f.debug_tuple("Encoding").field(e).finish(),
            Self::Validation(e) => f.debug_tuple("Validation").field(e).finish(),
            Self::Runtime(e) => f.debug_tuple("Runtime").field(e).finish(),
            Self::Infrastructure(e) => f.debug_tuple("Infrastructure").field(e).finish(),
            Self::Script(e) => f.debug_tuple("Script").field(e).finish(),
        }
    }
}

impl From<ExecError> for Failure {
    fn from(error: ExecError) -> Self {
        Self::Runtime(error)
    }
}

type Result<T> = std::result::Result<T, Failure>;

struct Script {
    profile: ValidationProfile,
    store: Store,
    current: Option<InstanceAddr>,
    named: BTreeMap<String, InstanceAddr>,
    registered: BTreeMap<Vec<u8>, InstanceAddr>,
    spectest: BTreeMap<Vec<u8>, Extern>,
    references: BTreeMap<u32, ExternAddr>,
}

impl Script {
    fn new(profile: ValidationProfile) -> Result<Self> {
        let mut script = Self {
            profile,
            store: Store::with_limits(StoreLimits {
                max_values: 4_000_000,
                ..StoreLimits::default()
            }),
            current: None,
            named: BTreeMap::new(),
            registered: BTreeMap::new(),
            spectest: BTreeMap::new(),
            references: BTreeMap::new(),
        };
        let functions: &[(&str, &[ValueType])] = &[
            ("print", &[]),
            ("print_i32", &[ValueType::I32]),
            ("print_i64", &[ValueType::I64]),
            ("print_f32", &[ValueType::F32]),
            ("print_f64", &[ValueType::F64]),
            ("print_i32_f32", &[ValueType::I32, ValueType::F32]),
            ("print_f64_f64", &[ValueType::F64, ValueType::F64]),
        ];
        for (id, (name, params)) in functions.iter().enumerate() {
            let address = script.store.define_host(
                FuncType {
                    params: params.to_vec(),
                    results: vec![],
                },
                id as u64,
            )?;
            script
                .spectest
                .insert(name.as_bytes().to_vec(), Extern::Func(address));
        }
        for (name, valtype, value) in [
            ("global_i32", ValueType::I32, Value::I32(666)),
            ("global_i64", ValueType::I64, Value::I64(666)),
            (
                "global_f32",
                ValueType::F32,
                Value::F32(666.6_f32.to_bits()),
            ),
            (
                "global_f64",
                ValueType::F64,
                Value::F64(666.6_f64.to_bits()),
            ),
        ] {
            let address = script.store.define_global(
                GlobalType {
                    valtype,
                    mutability: Mut::Const,
                },
                value,
            )?;
            script
                .spectest
                .insert(name.as_bytes().to_vec(), Extern::Global(address));
        }
        let table = script.store.define_table(TableType {
            elem: ElemType::FuncRef,
            limits: Limits {
                min: 10,
                max: Some(20),
            },
        })?;
        script
            .spectest
            .insert(b"table".to_vec(), Extern::Table(table));
        let memory = script.store.define_memory(
            MemType {
                limits: Limits {
                    min: 1,
                    max: Some(2),
                },
            },
            VecMemory::new_zeroed(65536).expect("spectest memory allocation"),
        )?;
        script
            .spectest
            .insert(b"memory".to_vec(), Extern::Memory(memory));
        Ok(script)
    }

    fn encode(&self, mut module: QuoteWat<'_>) -> Result<Vec<u8>> {
        // Wasm 1 names immediately following `data`/`elem` denote the target
        // memory/table. Current wast parses those as segment names instead.
        // Recover that historical syntax in the AST before name resolution.
        if self.profile == ValidationProfile::Wasm1 {
            if let QuoteWat::Wat(Wat::Module(m)) = &mut module {
                if let ModuleKind::Text(fields) = &mut m.kind {
                    for field in fields {
                        match field {
                            ModuleField::Data(data) => {
                                if let (Some(id), DataKind::Active { memory, .. }) =
                                    (data.id.take(), &mut data.kind)
                                {
                                    *memory = wast::token::Index::Id(id);
                                }
                            }
                            ModuleField::Elem(elem) => {
                                if let (Some(id), ElemKind::Active { table, .. }) =
                                    (elem.id.take(), &mut elem.kind)
                                {
                                    *table = Some(wast::token::Index::Id(id));
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
        }
        // Literal binary fixtures must remain verbatim, including malformed
        // encodings. Only generated Wasm 1 text uses the existing normalization.
        let literal = matches!(&module, QuoteWat::Wat(Wat::Module(m)) if matches!(m.kind, ModuleKind::Binary(_)));
        let bytes = module
            .encode()
            .map_err(|e| Failure::Encoding(e.to_string()))?;
        if self.profile == ValidationProfile::Wasm1 && !literal {
            match crate::mvp_binary::normalize_to_wasm1(&bytes) {
                Ok(bytes) => Ok(bytes),
                // Invalid constant-expression fixtures are intentionally not
                // accepted by the valid-expression normalizer. Their ordinary
                // implicit-zero segment encoding is also the original Wasm 1
                // encoding; retain those bytes and require validator rejection.
                Err(_) if itasca::validate_module(&bytes, self.profile).is_err() => Ok(bytes),
                Err(e) => Err(Failure::Encoding(e.0)),
            }
        } else {
            Ok(bytes)
        }
    }

    fn compile(&self, module: QuoteWat<'_>) -> Result<ExecutableModule> {
        let bytes = self.encode(module)?;
        compile(&bytes, self.profile).map_err(Failure::Validation)
    }

    fn instantiate(&mut self, module: QuoteWat<'_>) -> Result<InstanceAddr> {
        let code = self.compile(module)?;
        let mut imports = Vec::new();
        for import in code.env().imports() {
            let item = if let Some(instance) = self.registered.get(&import.module) {
                self.store.export(*instance, &import.name)?
            } else if import.module == b"spectest" {
                self.spectest.get(&import.name).copied()
            } else {
                None
            };
            imports.push(item.ok_or(ExecError::Link(LinkError::MissingImport))?);
        }
        let mut platform = SpectestPlatform::new();
        let result = self
            .store
            .instantiate(code, &imports, &mut platform)
            .and_then(|instantiated| {
                if let Some(start) = instantiated.start {
                    Execution::new().invoke(
                        &mut self.store,
                        &mut platform,
                        start,
                        &[],
                        &mut Vec::new(),
                    )?;
                }
                Ok(instantiated.instance)
            });
        platform.check()?;
        result.map_err(Failure::Runtime)
    }

    fn instance(&self, id: Option<wast::token::Id<'_>>) -> Result<InstanceAddr> {
        match id {
            Some(id) => self.named.get(id.name()).copied(),
            None => self.current,
        }
        .ok_or_else(|| Failure::Script(format!("unknown instance {id:?}")))
    }

    fn argument(&mut self, arg: &WastArg<'_>) -> Result<Value> {
        let WastArg::Core(arg) = arg else {
            return Err(Failure::Script(format!("unsupported argument {arg:?}")));
        };
        Ok(match arg {
            WastArgCore::I32(x) => Value::I32(*x as u32),
            WastArgCore::I64(x) => Value::I64(*x as u64),
            WastArgCore::F32(x) => Value::F32(x.bits),
            WastArgCore::F64(x) => Value::F64(x.bits),
            WastArgCore::V128(x) => Value::V128(u128::from_le_bytes(x.to_le_bytes())),
            WastArgCore::RefNull(HeapType::Abstract {
                shared: false,
                ty: AbstractHeapType::Func,
            }) => Value::FuncRef(None),
            WastArgCore::RefNull(HeapType::Abstract {
                shared: false,
                ty: AbstractHeapType::Extern,
            }) => Value::ExternRef(None),
            WastArgCore::RefExtern(id) => {
                let reference = if let Some(reference) = self.references.get(id) {
                    *reference
                } else {
                    let reference = self.store.define_extern(*id as u64)?;
                    self.references.insert(*id, reference);
                    reference
                };
                Value::ExternRef(Some(reference))
            }
            other => return Err(Failure::Script(format!("unsupported argument {other:?}"))),
        })
    }

    fn invoke(&mut self, call: WastInvoke<'_>) -> Result<Vec<Value>> {
        let instance = self.instance(call.module)?;
        let Some(Extern::Func(function)) = self.store.export(instance, call.name.as_bytes())?
        else {
            return Err(Failure::Script(format!(
                "unknown function export {:?}",
                call.name
            )));
        };
        let arguments = call
            .args
            .iter()
            .map(|arg| self.argument(arg))
            .collect::<Result<Vec<_>>>()?;
        let mut platform = SpectestPlatform::new();
        let mut values = Vec::new();
        let result = Execution::new().invoke(
            &mut self.store,
            &mut platform,
            function,
            &arguments,
            &mut values,
        );
        platform.check()?;
        result.map_err(Failure::Runtime)?;
        Ok(values)
    }

    fn execute(&mut self, action: WastExecute<'_>) -> Result<Vec<Value>> {
        match action {
            WastExecute::Invoke(call) => self.invoke(call),
            WastExecute::Wat(module) => {
                self.instantiate(QuoteWat::Wat(module))?;
                Ok(vec![])
            }
            WastExecute::Get { module, global, .. } => {
                let instance = self.instance(module)?;
                let Some(Extern::Global(global)) =
                    self.store.export(instance, global.as_bytes())?
                else {
                    return Err(Failure::Script(format!("unknown global export {global:?}")));
                };
                Ok(vec![self.store.global(global)?])
            }
        }
    }

    fn matches(&self, actual: Value, expected: &WastRetCore<'_>) -> bool {
        match (actual, expected) {
            (Value::I32(a), WastRetCore::I32(e)) => a == *e as u32,
            (Value::I64(a), WastRetCore::I64(e)) => a == *e as u64,
            (Value::F32(a), WastRetCore::F32(e)) => f32_matches(a, e),
            (Value::F64(a), WastRetCore::F64(e)) => f64_matches(a, e),
            (Value::V128(a), WastRetCore::V128(e)) => vector_matches(a, e),
            (Value::FuncRef(None) | Value::ExternRef(None), WastRetCore::RefNull(None)) => true,
            (
                Value::FuncRef(None),
                WastRetCore::RefNull(Some(HeapType::Abstract {
                    shared: false,
                    ty: AbstractHeapType::Func,
                })),
            ) => true,
            (
                Value::ExternRef(None),
                WastRetCore::RefNull(Some(HeapType::Abstract {
                    shared: false,
                    ty: AbstractHeapType::Extern,
                })),
            ) => true,
            (Value::FuncRef(Some(_)), WastRetCore::RefFunc(None)) => true,
            (Value::ExternRef(Some(_)), WastRetCore::RefExtern(None)) => true,
            (Value::ExternRef(Some(a)), WastRetCore::RefExtern(Some(e))) => {
                self.store.extern_identity(a).ok() == Some(*e as u64)
            }
            (a, WastRetCore::Either(options)) => options.iter().any(|e| self.matches(a, e)),
            _ => false,
        }
    }
}

fn f32_matches(actual: u32, expected: &NanPattern<wast::token::F32>) -> bool {
    match expected {
        NanPattern::Value(expected) => actual == expected.bits,
        NanPattern::CanonicalNan => actual & 0x7fff_ffff == 0x7fc0_0000,
        NanPattern::ArithmeticNan => actual & 0x7fc0_0000 == 0x7fc0_0000,
    }
}

fn f64_matches(actual: u64, expected: &NanPattern<wast::token::F64>) -> bool {
    match expected {
        NanPattern::Value(expected) => actual == expected.bits,
        NanPattern::CanonicalNan => actual & 0x7fff_ffff_ffff_ffff == 0x7ff8_0000_0000_0000,
        NanPattern::ArithmeticNan => actual & 0x7ff8_0000_0000_0000 == 0x7ff8_0000_0000_0000,
    }
}

fn vector_matches(actual: u128, expected: &V128Pattern) -> bool {
    match expected {
        V128Pattern::I8x16(lanes) => lanes
            .iter()
            .enumerate()
            .all(|(i, e)| (actual >> (8 * i)) as u8 == *e as u8),
        V128Pattern::I16x8(lanes) => lanes
            .iter()
            .enumerate()
            .all(|(i, e)| (actual >> (16 * i)) as u16 == *e as u16),
        V128Pattern::I32x4(lanes) => lanes
            .iter()
            .enumerate()
            .all(|(i, e)| (actual >> (32 * i)) as u32 == *e as u32),
        V128Pattern::I64x2(lanes) => lanes
            .iter()
            .enumerate()
            .all(|(i, e)| (actual >> (64 * i)) as u64 == *e as u64),
        V128Pattern::F32x4(lanes) => lanes
            .iter()
            .enumerate()
            .all(|(i, e)| f32_matches((actual >> (32 * i)) as u32, e)),
        V128Pattern::F64x2(lanes) => lanes
            .iter()
            .enumerate()
            .all(|(i, e)| f64_matches((actual >> (64 * i)) as u64, e)),
    }
}

fn expected_trap(message: &str) -> Option<Trap> {
    if message
        .strip_prefix("uninitialized element ")
        .is_some_and(|suffix| suffix.parse::<u32>().is_ok())
    {
        return Some(Trap::UninitializedElement);
    }
    Some(match message {
        "unreachable" => Trap::Unreachable,
        "integer divide by zero" => Trap::IntegerDivideByZero,
        "integer overflow" => Trap::IntegerOverflow,
        "invalid conversion to integer" => Trap::InvalidConversionToInteger,
        "out of bounds memory access" | "data segment does not fit" => Trap::MemoryOutOfBounds,
        "out of bounds table access"
        | "undefined element"
        | "undefined"
        | "elements segment does not fit" => Trap::TableOutOfBounds,
        "uninitialized element" | "uninitialized" => Trap::UninitializedElement,
        "indirect call type mismatch" | "indirect call" => Trap::IndirectCallTypeMismatch,
        _ => return None,
    })
}

// The old corpus spells NaN assertions with separate directives, which modern
// wast no longer parses. Rewrite just that keyword, preserving every byte
// coordinate and retain the original assertion kind to check the actual result.
fn legacy_nan_source(source: &str) -> (String, BTreeMap<usize, bool>) {
    let mut bytes = source.as_bytes().to_vec();
    let mut legacy = BTreeMap::new();
    let mut i = 0;
    let mut depth = 0;
    while i < bytes.len() {
        match bytes[i] {
            b';' if bytes.get(i + 1) == Some(&b';') => {
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
            }
            b'(' if bytes.get(i + 1) == Some(&b';') => {
                let mut nested = 1;
                i += 2;
                while i < bytes.len() && nested > 0 {
                    if bytes[i..].starts_with(b"(;") {
                        nested += 1;
                        i += 2;
                    } else if bytes[i..].starts_with(b";)") {
                        nested -= 1;
                        i += 2;
                    } else {
                        i += 1;
                    }
                }
            }
            b'"' => {
                i += 1;
                while i < bytes.len() && bytes[i] != b'"' {
                    i += if bytes[i] == b'\\' { 2 } else { 1 };
                }
                i += 1;
            }
            b'(' => {
                if depth == 0 {
                    let mut start = i + 1;
                    while bytes.get(start).is_some_and(u8::is_ascii_whitespace) {
                        start += 1;
                    }
                    for (keyword, canonical) in [
                        ("assert_return_canonical_nan", true),
                        ("assert_return_arithmetic_nan", false),
                    ] {
                        if bytes[start..].starts_with(keyword.as_bytes()) {
                            bytes[start..start + keyword.len()].fill(b' ');
                            bytes[start..start + "assert_return".len()]
                                .copy_from_slice(b"assert_return");
                            legacy.insert(start, canonical);
                        }
                    }
                }
                depth += 1;
                i += 1;
            }
            b')' => {
                depth -= 1;
                i += 1;
            }
            _ => i += 1,
        }
    }
    (String::from_utf8(bytes).unwrap(), legacy)
}

fn assertion(
    script: &mut Script,
    directive: WastDirective<'_>,
    legacy: Option<bool>,
    counts: &mut Counts,
) -> std::result::Result<(), String> {
    match directive {
        WastDirective::Module(module) => {
            let name = module.name().map(|id| id.name().to_owned());
            let instance = script
                .instantiate(module)
                .map_err(|e| format!("expected successful module instantiation, got {e:?}"))?;
            if let Some(name) = name {
                script.named.insert(name, instance);
            }
            script.current = Some(instance);
            counts.modules += 1;
        }
        WastDirective::Register { name, module, .. } => {
            let instance = script
                .instance(module)
                .map_err(|e| format!("registration: {e:?}"))?;
            script.registered.insert(name.as_bytes().to_vec(), instance);
            counts.registrations += 1;
        }
        WastDirective::Invoke(call) => {
            script
                .invoke(call)
                .map_err(|e| format!("expected invocation success, got {e:?}"))?;
            counts.invocations += 1;
        }
        WastDirective::AssertReturn { exec, results, .. } => {
            let values = script
                .execute(exec)
                .map_err(|e| format!("expected return {results:?}, got {e:?}"))?;
            if let Some(canonical) = legacy {
                let matched = match values.as_slice() {
                    [Value::F32(a)] => f32_matches(
                        *a,
                        &if canonical {
                            NanPattern::CanonicalNan
                        } else {
                            NanPattern::ArithmeticNan
                        },
                    ),
                    [Value::F64(a)] => f64_matches(
                        *a,
                        &if canonical {
                            NanPattern::CanonicalNan
                        } else {
                            NanPattern::ArithmeticNan
                        },
                    ),
                    _ => false,
                };
                if !matched {
                    return Err(format!(
                        "expected legacy {} NaN, got {values:?}",
                        if canonical { "canonical" } else { "arithmetic" }
                    ));
                }
                counts.legacy_nan += 1;
            } else {
                let matched = values.len() == results.len()
                    && values
                        .iter()
                        .zip(&results)
                        .all(|(actual, expected)| match expected {
                            WastRet::Core(expected) => script.matches(*actual, expected),
                            _ => false,
                        });
                if !matched {
                    return Err(format!("expected {results:?}, got {values:?}"));
                }
                counts.returns += 1;
            }
        }
        WastDirective::AssertTrap { exec, message, .. } => {
            let result = script.execute(exec);
            let Some(expected) = expected_trap(message) else {
                return Err(format!("unmapped expected trap {message:?}"));
            };
            if !matches!(&result, Err(Failure::Runtime(ExecError::Trap(actual))) if *actual == expected)
            {
                return Err(format!(
                    "expected Wasm trap {message:?} ({expected:?}), got {result:?}"
                ));
            }
            counts.traps += 1;
        }
        WastDirective::AssertExhaustion { call, message, .. } => {
            let result = script.invoke(call);
            if message != "call stack exhausted"
                || !matches!(
                    result,
                    Err(Failure::Runtime(ExecError::Exhausted(
                        ResourceLimit::CallStack
                    )))
                )
            {
                return Err(format!(
                    "expected stack exhaustion {message:?}, got {result:?}"
                ));
            }
            counts.exhaustion += 1;
        }
        WastDirective::AssertUnlinkable {
            module, message, ..
        } => {
            // The old script grammar calls prechecked active-segment bounds
            // failures unlinkable. The runtime exposes the same bounds reason
            // as a trap while preserving Wasm 1's all-or-nothing segment writes.
            if script.profile == ValidationProfile::Wasm1
                && matches!(
                    message,
                    "data segment does not fit" | "elements segment does not fit"
                )
            {
                let result = script.instantiate(QuoteWat::Wat(module));
                if !matches!(&result, Err(Failure::Runtime(ExecError::Trap(actual))) if Some(*actual) == expected_trap(message))
                {
                    return Err(format!(
                        "expected historical segment link failure {message:?}, got {result:?}"
                    ));
                }
                counts.unlinkable += 1;
                return Ok(());
            }
            let expected = match message {
                "unknown import" => LinkError::MissingImport,
                "incompatible import type" => LinkError::IncompatibleImportType,
                _ => return Err(format!("unmapped expected link failure {message:?}")),
            };
            let result = script.instantiate(QuoteWat::Wat(module));
            if !matches!(&result, Err(Failure::Runtime(ExecError::Link(actual))) if *actual == expected)
            {
                return Err(format!("expected link failure {message:?}, got {result:?}"));
            }
            counts.unlinkable += 1;
        }
        WastDirective::AssertInvalid {
            module, message, ..
        } => {
            let result = script.compile(module);
            if !matches!(result, Err(Failure::Validation(_))) {
                return Err(format!(
                    "expected validation rejection {message:?}, got {result:?}"
                ));
            }
            counts.invalid += 1;
        }
        WastDirective::AssertMalformed {
            module, message, ..
        } => {
            let quoted = matches!(module, QuoteWat::QuoteModule(..));
            match script.compile(module) {
                Err(Failure::Encoding(_)) if quoted => counts.malformed_text += 1,
                Err(Failure::Validation(_)) => counts.malformed_binary += 1,
                actual => {
                    return Err(format!(
                        "expected malformed module {message:?}, got {actual:?}"
                    ))
                }
            }
        }
        other => {
            counts.unsupported += 1;
            return Err(format!("unsupported directive: {other:?}"));
        }
    }
    Ok(())
}

fn collect_wast(dir: &Path, files: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            collect_wast(&path, files);
        } else if path.extension().is_some_and(|ext| ext == "wast") {
            files.push(path);
        }
    }
}

pub fn run_corpus(directory: &str, profile: ValidationProfile) {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join(directory);
    let mut files = Vec::new();
    collect_wast(&root, &mut files);
    files.sort();
    let filter = std::env::var("ITASCA_WAST_FILE").ok();
    if let Some(filter) = &filter {
        files.retain(|file| file.to_string_lossy().contains(filter));
    }
    assert!(!files.is_empty(), "no WAST files matched");
    let mut counts = Counts::default();
    let mut failures = Vec::new();
    for path in files {
        let original = std::fs::read_to_string(&path).unwrap();
        let (source, legacy) = legacy_nan_source(&original);
        let mut lexer = wast::lexer::Lexer::new(&source);
        lexer.allow_confusing_unicode(true);
        let buffer = wast::parser::ParseBuffer::new_with_lexer(lexer)
            .unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        let parsed = wast::parser::parse::<Wast>(&buffer)
            .unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        let mut script = Script::new(profile).unwrap();
        for (index, directive) in parsed.directives.into_iter().enumerate() {
            let span = directive.span();
            let (line, column) = span.linecol_in(&source);
            let kind = format!("{directive:?}");
            let kind = kind.split([' ', '(', '{']).next().unwrap_or("directive");
            if let Err(error) = assertion(
                &mut script,
                directive,
                legacy.get(&span.offset()).copied(),
                &mut counts,
            ) {
                failures.push(format!(
                    "{}:{}:{} [{profile:?}] directive {} ({kind}): {error}",
                    path.display(),
                    line + 1,
                    column + 1,
                    index + 1
                ));
                // Later actions depend on this state. Report the script failure,
                // never count its remaining assertions as successful.
                break;
            }
        }
        counts.files += 1;
    }
    eprintln!("{profile:?} executed: {counts:?}");
    for failure in &failures {
        eprintln!("{failure}");
    }
    assert!(
        failures.is_empty(),
        "{} WAST scripts failed",
        failures.len()
    );
    assert_eq!(counts.unsupported, 0);
    if filter.is_none() {
        let expected = if profile == ValidationProfile::Wasm1 {
            Counts {
                files: 73,
                modules: 780,
                malformed_text: 429,
                malformed_binary: 662,
                invalid: 989,
                registrations: 10,
                invocations: 42,
                returns: 13894,
                traps: 460,
                unlinkable: 95,
                exhaustion: 15,
                legacy_nan: 1894,
                unsupported: 0,
            }
        } else {
            Counts {
                files: 148,
                modules: 1599,
                malformed_text: 1081,
                malformed_binary: 729,
                invalid: 2146,
                registrations: 22,
                invocations: 155,
                returns: 45734,
                traps: 2442,
                unlinkable: 83,
                exhaustion: 15,
                legacy_nan: 0,
                unsupported: 0,
            }
        };
        assert_eq!(counts, expected, "pinned execution coverage changed");
    }
}
