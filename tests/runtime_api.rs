use itasca::runtime::*;
use itasca::{
    ElemType, FuncType, GlobalType, Limits, MemType, Mut, TableType, ValidationProfile, ValueType,
};

struct Hooks {
    remaining: usize,
}
impl Hooks {
    fn new() -> Self {
        Self { remaining: 100_000 }
    }
}
impl<M: MemoryBuffer> Platform<M> for Hooks {
    fn interrupt(&mut self) -> InterruptAction {
        if self.remaining == 0 {
            InterruptAction::Terminate
        } else {
            self.remaining -= 1;
            InterruptAction::Continue
        }
    }
    fn call_host(
        &mut self,
        _: &mut Store<M>,
        _: u64,
        _: &[Value],
        _: &mut [Value],
    ) -> Result<(), HostError> {
        Err(HostError::Trap)
    }
}
fn module(wat: &str, profile: ValidationProfile) -> ExecutableModule {
    let buf = wast::parser::ParseBuffer::new(wat).unwrap();
    let mut ast = wast::parser::parse::<wast::Wat>(&buf).unwrap();
    compile(&ast.encode().unwrap(), profile).unwrap()
}
fn instance(store: &mut Store, wat: &str, imports: &[Extern]) -> InstanceAddr {
    store
        .instantiate(
            module(wat, ValidationProfile::Wasm2),
            imports,
            &mut Hooks::new(),
        )
        .unwrap()
        .instance
}
fn func<M: MemoryBuffer>(store: &Store<M>, i: InstanceAddr, name: &str) -> FuncAddr {
    match store.export(i, name.as_bytes()).unwrap().unwrap() {
        Extern::Func(f) => f,
        _ => panic!("not function"),
    }
}
fn invoke(store: &mut Store, f: FuncAddr, args: &[Value]) -> Result<Vec<Value>, ExecError> {
    let mut results = Vec::new();
    Execution::new().invoke(store, &mut Hooks::new(), f, args, &mut results)?;
    Ok(results)
}
fn run(store: &mut Store, f: FuncAddr, args: &[Value]) -> Vec<Value> {
    invoke(store, f, args).unwrap()
}

#[test]
fn cross_instance_calls_use_defining_globals_memory_and_functions() {
    let mut store = Store::new();
    let provider = instance(
        &mut store,
        r#"(module
        (global i32 (i32.const 31)) (memory (export "memory") 1)
        (data (i32.const 0) "\07\00\00\00")
        (func $helper (result i32) global.get 0 i32.const 0 i32.load i32.add)
        (func (export "get") (result i32) call $helper)
        (table (export "table") 1 funcref) (elem (i32.const 0) 1))"#,
        &[],
    );
    let f = func(&store, provider, "get");
    let table = store.export(provider, b"table").unwrap().unwrap();
    let consumer = instance(
        &mut store,
        r#"(module
        (type (func (result i32))) (import "p" "get" (func $get (type 0)))
        (import "p" "table" (table 1 funcref)) (global i32 (i32.const 99)) (memory 1)
        (func (export "direct") (result i32) call $get)
        (func (export "indirect") (result i32) i32.const 0 call_indirect (type 0)))"#,
        &[Extern::Func(f), table],
    );
    let direct = func(&store, consumer, "direct");
    let indirect = func(&store, consumer, "indirect");
    assert_eq!(run(&mut store, direct, &[]), [Value::I32(38)]);
    assert_eq!(run(&mut store, indirect, &[]), [Value::I32(38)]);
}
#[test]
fn failed_segments_preserve_profile_specific_effects_and_escaped_functions() {
    let wat = r#"(module (import "h" "t" (table 1 funcref)) (import "h" "m" (memory 1))
      (global i32 (i32.const 77)) (func (result i32) global.get 0)
      (elem (i32.const 0) 0) (data (i32.const 0) "A") (data (i32.const 65536) "B"))"#;
    for profile in [ValidationProfile::Wasm1, ValidationProfile::Wasm2] {
        let mut store = Store::new();
        let table = store
            .define_table(TableType {
                elem: ElemType::FuncRef,
                limits: Limits { min: 1, max: None },
            })
            .unwrap();
        let memory = store
            .define_memory(
                MemType {
                    limits: Limits { min: 1, max: None },
                },
                VecMemory::new_zeroed(65536).unwrap(),
            )
            .unwrap();
        assert!(matches!(
            store.instantiate(
                module(wat, profile),
                &[Extern::Table(table), Extern::Memory(memory)],
                &mut Hooks::new()
            ),
            Err(ExecError::Trap(Trap::MemoryOutOfBounds))
        ));
        if profile == ValidationProfile::Wasm1 {
            assert_eq!(store.memory(memory).unwrap()[0], 0);
            assert_eq!(store.table_get(table, 0).unwrap(), Value::FuncRef(None));
        } else {
            assert_eq!(store.memory(memory).unwrap()[0], b'A');
            let f = match store.table_get(table, 0).unwrap() {
                Value::FuncRef(Some(f)) => f,
                _ => panic!(),
            };
            assert_eq!(run(&mut store, f, &[]), [Value::I32(77)]);
        }
    }
}
#[test]
fn dropped_segments_are_empty_and_zero_length_bounds_are_checked() {
    let mut store = Store::new();
    let i = instance(
        &mut store,
        r#"(module (memory (export "m") 1) (data $d "abc")
      (func (export "drop") data.drop $d)
      (func (export "init") (param i32 i32 i32) local.get 0 local.get 1 local.get 2 memory.init $d))"#,
        &[],
    );
    let drop = func(&store, i, "drop");
    let init = func(&store, i, "init");
    run(&mut store, drop, &[]);
    assert!(run(
        &mut store,
        init,
        &[Value::I32(65536), Value::I32(0), Value::I32(0)]
    )
    .is_empty());
    assert_eq!(
        invoke(
            &mut store,
            init,
            &[Value::I32(0), Value::I32(1), Value::I32(0)]
        ),
        Err(ExecError::Trap(Trap::MemoryOutOfBounds))
    );
}

#[test]
fn trap_does_not_undo_prior_memory_effects() {
    let mut store = Store::new();
    let i = instance(
        &mut store,
        r#"(module (memory (export "m") 1)
       (func (export "f") i32.const 0 i32.const 55 i32.store8 unreachable))"#,
        &[],
    );
    let f = func(&store, i, "f");
    assert_eq!(
        invoke(&mut store, f, &[]),
        Err(ExecError::Trap(Trap::Unreachable))
    );
    let m = match store.export(i, b"m").unwrap().unwrap() {
        Extern::Memory(m) => m,
        _ => panic!(),
    };
    assert_eq!(store.memory(m).unwrap()[0], 55);
}

#[test]
fn wrong_store_and_foreign_references_are_rejected() {
    let mut a: Store = Store::new();
    let mut b = Store::new();
    let f = a
        .define_host(
            FuncType {
                params: vec![],
                results: vec![],
            },
            0,
        )
        .unwrap();
    assert_eq!(invoke(&mut b, f, &[]), Err(ExecError::WrongStore));
    let ext = a.define_extern(4).unwrap();
    assert_eq!(
        b.define_global(
            GlobalType {
                mutability: Mut::Const,
                valtype: ValueType::ExternRef
            },
            Value::ExternRef(Some(ext))
        ),
        Err(ExecError::WrongStore)
    );
}

#[test]
fn frame_exhaustion_is_distinct_from_interrupt_termination() {
    let mut store = Store::with_limits(StoreLimits {
        max_frames: 3,
        ..Default::default()
    });
    let i = instance(
        &mut store,
        r#"(module (func $f (export "f") call $f))"#,
        &[],
    );
    let f = func(&store, i, "f");
    assert_eq!(
        invoke(&mut store, f, &[]),
        Err(ExecError::Exhausted(ResourceLimit::CallStack))
    );
    let mut results = Vec::new();
    assert_eq!(
        Execution::new().invoke(
            &mut store,
            &mut Hooks { remaining: 0 },
            f,
            &[],
            &mut results
        ),
        Err(ExecError::Terminated)
    );
}

#[test]
fn loop_interrupt_retains_completed_memory_effects() {
    let mut store = Store::new();
    let i = instance(
        &mut store,
        r#"(module (memory (export "m") 1)
        (func (export "run") i32.const 0 i32.const 42 i32.store8 loop br 0 end))"#,
        &[],
    );
    let f = func(&store, i, "run");
    let mut results = Vec::new();
    assert_eq!(
        Execution::new().invoke(
            &mut store,
            &mut Hooks { remaining: 3 },
            f,
            &[],
            &mut results
        ),
        Err(ExecError::Terminated)
    );
    let Extern::Memory(m) = store.export(i, b"m").unwrap().unwrap() else {
        panic!()
    };
    assert_eq!(store.memory(m).unwrap()[0], 42);
}

struct Reenter {
    nested: FuncAddr,
    calls: usize,
}
impl Platform<VecMemory> for Reenter {
    fn interrupt(&mut self) -> InterruptAction {
        InterruptAction::Continue
    }
    fn call_host(
        &mut self,
        store: &mut Store,
        id: u64,
        args: &[Value],
        results: &mut [Value],
    ) -> Result<(), HostError> {
        self.calls += 1;
        assert_eq!(id, 5);
        assert_eq!(args, [Value::I32(3)]);
        let mut nested = Vec::new();
        Execution::new()
            .invoke(store, self, self.nested, &[Value::I32(9)], &mut nested)
            .unwrap();
        assert_eq!(nested, [Value::I32(10)]);
        results[0] = Value::I32(6);
        Ok(())
    }
}
#[test]
fn host_calls_reenter_without_replaying_outer_effects() {
    let mut store = Store::new();
    let host = store
        .define_host(
            FuncType {
                params: vec![ValueType::I32],
                results: vec![ValueType::I32],
            },
            5,
        )
        .unwrap();
    let i = instance(
        &mut store,
        r#"(module
        (import "h" "f" (func $host (param i32) (result i32)))
        (func (export "nested") (param i32) (result i32) local.get 0 i32.const 1 i32.add)
        (func (export "run") (result i32) i32.const 3 call $host i32.const 1 i32.add))"#,
        &[Extern::Func(host)],
    );
    let mut hooks = Reenter {
        nested: func(&store, i, "nested"),
        calls: 0,
    };
    let f = func(&store, i, "run");
    let mut results = Vec::new();
    Execution::new()
        .invoke(&mut store, &mut hooks, f, &[], &mut results)
        .unwrap();
    assert_eq!(results, [Value::I32(7)]);
    assert_eq!(hooks.calls, 1);
}

struct HostReply {
    value: Value,
    overflow: bool,
}
impl Platform<VecMemory> for HostReply {
    fn interrupt(&mut self) -> InterruptAction {
        InterruptAction::Continue
    }
    fn call_host(
        &mut self,
        _: &mut Store,
        _: u64,
        _: &[Value],
        results: &mut [Value],
    ) -> Result<(), HostError> {
        if self.overflow {
            return Err(HostError::StackOverflow);
        }
        results[0] = self.value;
        Ok(())
    }
}
#[test]
fn host_results_are_checked_and_stack_overflow_is_exhaustion() {
    let mut store = Store::new();
    let host = store
        .define_host(
            FuncType {
                params: vec![],
                results: vec![ValueType::I32],
            },
            0,
        )
        .unwrap();
    let mut results = Vec::new();
    let mut hooks = HostReply {
        value: Value::I64(0),
        overflow: false,
    };
    assert!(matches!(
        Execution::new().invoke(&mut store, &mut hooks, host, &[], &mut results),
        Err(ExecError::Trap(_))
    ));
    hooks.overflow = true;
    assert!(matches!(
        Execution::new().invoke(&mut store, &mut hooks, host, &[], &mut results),
        Err(ExecError::Exhausted(_))
    ));
}

struct FixedMemory(Vec<u8>);
impl MemoryBuffer for FixedMemory {
    fn new_zeroed(len: usize) -> Option<Self> {
        Some(Self(vec![0; len]))
    }
    fn bytes(&self) -> &[u8] {
        &self.0
    }
    fn bytes_mut(&mut self) -> &mut [u8] {
        &mut self.0
    }
    fn grow(&mut self, new_len: usize) -> bool {
        if new_len > 2 * 65536 {
            return false;
        }
        self.0.resize(new_len, 0);
        true
    }
}
#[test]
fn embedder_memory_growth_preserves_bytes_and_zero_fills() {
    let mut store = Store::<FixedMemory>::new();
    let m = store
        .define_memory(
            MemType {
                limits: Limits { min: 1, max: None },
            },
            FixedMemory::new_zeroed(65536).unwrap(),
        )
        .unwrap();
    store.memory_mut(m).unwrap()[0] = 99;
    let i = store
        .instantiate(
            module(
                r#"(module (import "h" "m" (memory 1))
        (func (export "grow") (result i32) i32.const 1 memory.grow))"#,
                ValidationProfile::Wasm2,
            ),
            &[Extern::Memory(m)],
            &mut Hooks::new(),
        )
        .unwrap()
        .instance;
    let f = func(&store, i, "grow");
    let mut results = Vec::new();
    let mut e = Execution::new();
    e.invoke(&mut store, &mut Hooks::new(), f, &[], &mut results)
        .unwrap();
    assert_eq!(results, [Value::I32(1)]);
    assert_eq!(store.memory(m).unwrap()[0], 99);
    assert!(store.memory(m).unwrap()[65536..].iter().all(|b| *b == 0));
    e.invoke(&mut store, &mut Hooks::new(), f, &[], &mut results)
        .unwrap();
    assert_eq!(results, [Value::I32(u32::MAX)]);
    assert_eq!(store.memory(m).unwrap().len(), 2 * 65536);
}

#[test]
fn start_function_runs_after_segment_initialization() {
    struct Start {
        memory: MemoryAddr,
        calls: usize,
    }
    impl Platform<VecMemory> for Start {
        fn interrupt(&mut self) -> InterruptAction {
            InterruptAction::Continue
        }
        fn call_host(
            &mut self,
            store: &mut Store,
            _: u64,
            _: &[Value],
            _: &mut [Value],
        ) -> Result<(), HostError> {
            self.calls += 1;
            assert_eq!(store.memory(self.memory).unwrap()[0], b'A');
            store.memory_mut(self.memory).unwrap()[1] = b'B';
            Ok(())
        }
    }
    let mut store = Store::new();
    let memory = store
        .define_memory(
            MemType {
                limits: Limits { min: 1, max: None },
            },
            VecMemory::new_zeroed(65536).unwrap(),
        )
        .unwrap();
    let host = store
        .define_host(
            FuncType {
                params: vec![],
                results: vec![],
            },
            0,
        )
        .unwrap();
    let mut platform = Start { memory, calls: 0 };
    let instantiated = store
        .instantiate(
            module(
                r#"(module (import "h" "m" (memory 1))
        (import "h" "start" (func $start)) (data (i32.const 0) "A") (start $start))"#,
                ValidationProfile::Wasm2,
            ),
            &[Extern::Memory(memory), Extern::Func(host)],
            &mut platform,
        )
        .unwrap();
    assert_eq!(platform.calls, 0);
    assert_eq!(store.memory(memory).unwrap()[0], b'A');
    let start = instantiated.start.unwrap();
    Execution::new()
        .invoke(&mut store, &mut platform, start, &[], &mut Vec::new())
        .unwrap();
    assert_eq!(platform.calls, 1);
    assert_eq!(&store.memory(memory).unwrap()[..2], b"AB");
}

#[test]
fn execution_storage_is_reusable_after_traps_and_argument_rejection() {
    let mut store = Store::new();
    let i = instance(
        &mut store,
        r#"(module
        (func (export "id") (param i32) (result i32) local.get 0)
        (func (export "trap") unreachable))"#,
        &[],
    );
    let id = func(&store, i, "id");
    let trap = func(&store, i, "trap");
    let mut e = Execution::new();
    let mut result = Vec::new();
    assert_eq!(
        e.invoke(&mut store, &mut Hooks::new(), trap, &[], &mut result),
        Err(ExecError::Trap(Trap::Unreachable))
    );
    assert_eq!(
        e.invoke(
            &mut store,
            &mut Hooks::new(),
            id,
            &[Value::I64(4)],
            &mut result
        ),
        Err(ExecError::BadArguments)
    );
    e.invoke(
        &mut store,
        &mut Hooks::new(),
        id,
        &[Value::I32(7)],
        &mut result,
    )
    .unwrap();
    assert_eq!(result, [Value::I32(7)]);
}

#[test]
fn host_table_changes_are_observed_by_subsequent_indirect_calls() {
    struct Replace {
        table: TableAddr,
        target: FuncAddr,
    }
    impl Platform<VecMemory> for Replace {
        fn interrupt(&mut self) -> InterruptAction {
            InterruptAction::Continue
        }
        fn call_host(
            &mut self,
            store: &mut Store,
            _: u64,
            _: &[Value],
            _: &mut [Value],
        ) -> Result<(), HostError> {
            store
                .set_table(self.table, 0, Value::FuncRef(Some(self.target)))
                .unwrap();
            Ok(())
        }
    }
    let mut store = Store::new();
    let host = store
        .define_host(
            FuncType {
                params: vec![],
                results: vec![],
            },
            0,
        )
        .unwrap();
    let i = instance(
        &mut store,
        r#"(module
        (type $t (func (result i32))) (import "h" "replace" (func $replace))
        (table (export "table") 1 funcref)
        (func $old (type $t) i32.const 99)
        (func $new (export "new") (type $t) i32.const 17)
        (elem (i32.const 0) $old)
        (func (export "run") (result i32) call $replace i32.const 0 call_indirect (type $t)))"#,
        &[Extern::Func(host)],
    );
    let Extern::Table(table) = store.export(i, b"table").unwrap().unwrap() else {
        panic!()
    };
    let f = func(&store, i, "run");
    let mut platform = Replace {
        table,
        target: func(&store, i, "new"),
    };
    let mut results = Vec::new();
    Execution::new()
        .invoke(&mut store, &mut platform, f, &[], &mut results)
        .unwrap();
    assert_eq!(results, [Value::I32(17)]);
}
