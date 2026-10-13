use itasca::runtime::*;
use itasca::{
    ElemType, FuncType, GlobalType, Limits, MemType, Mut, TableType, ValidationProfile, ValueType,
};
use std::rc::Rc;

fn module(wat: &str, profile: ValidationProfile) -> Rc<ExecutableModule> {
    let buf = wast::parser::ParseBuffer::new(wat).unwrap();
    let mut ast = wast::parser::parse::<wast::Wat>(&buf).unwrap();
    Rc::new(compile(&ast.encode().unwrap(), profile).unwrap())
}
fn instance(store: &mut Store, wat: &str, imports: &[Extern]) -> InstanceAddr {
    let mut pending = store
        .instantiate(module(wat, ValidationProfile::Wasm2), imports)
        .unwrap();
    pending.add_fuel(100_000).unwrap();
    assert!(matches!(pending.run(store), Outcome::Returned(_)));
    pending.instance().unwrap()
}
fn func(store: &Store, i: InstanceAddr, name: &str) -> FuncAddr {
    match store.export(i, name.as_bytes()).unwrap().unwrap() {
        Extern::Func(f) => f,
        _ => panic!("not function"),
    }
}
fn run(store: &mut Store, f: FuncAddr, args: &[Value]) -> Vec<Value> {
    let mut e = Execution::new(store, f, args).unwrap();
    e.add_fuel(100_000).unwrap();
    match e.run(store) {
        Outcome::Returned(v) => v,
        other => panic!("{other:?}"),
    }
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
fn fuel_suspends_before_bulk_effect_and_retains_insufficient_budget() {
    let mut store = Store::new();
    let i = instance(
        &mut store,
        r#"(module (memory (export "m") 1)
      (func (export "fill") i32.const 0 i32.const 42 i32.const 128 memory.fill))"#,
        &[],
    );
    let f = func(&store, i, "fill");
    let memory = match store.export(i, b"m").unwrap().unwrap() {
        Extern::Memory(m) => m,
        _ => unreachable!(),
    };
    let mut e = Execution::new(&store, f, &[]).unwrap();
    e.add_fuel(6).unwrap();
    assert!(matches!(e.run(&mut store), Outcome::Suspended));
    assert_eq!(e.fuel(), 2);
    assert_eq!(store.memory(memory).unwrap()[0], 0);
    assert!(matches!(e.run(&mut store), Outcome::Suspended));
    assert_eq!(e.fuel(), 2);
    e.add_fuel(1).unwrap();
    assert!(matches!(e.run(&mut store), Outcome::Suspended));
    assert_eq!(store.memory(memory).unwrap()[127], 42);
    assert_eq!(e.fuel(), 0);
    e.add_fuel(1).unwrap();
    assert!(matches!(e.run(&mut store), Outcome::Returned(_)));
    assert!(matches!(
        e.run(&mut store),
        Outcome::Failed(RuntimeError::InvalidState)
    ));
}
#[test]
fn host_resume_checks_types_ownership_and_is_not_replayed() {
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
        r#"(module (import "h" "f" (func $host (param i32) (result i32)))
        (func (export "f") (result i32) i32.const 3 call $host i32.const 1 i32.add))"#,
        &[Extern::Func(host)],
    );
    let mut e = Execution::new(&store, func(&store, i, "f"), &[]).unwrap();
    e.add_fuel(100).unwrap();
    match e.run(&mut store) {
        Outcome::NeedsHostCall(r) => {
            assert_eq!(r.host_id, 5);
            assert_eq!(r.arguments, [Value::I32(3)]);
        }
        x => panic!("{x:?}"),
    }
    let fuel = e.fuel();
    assert_eq!(
        e.resume_host(&store, Ok(&[Value::I64(6)])),
        Err(RuntimeError::TypeMismatch)
    );
    assert!(matches!(
        e.run(&mut store),
        Outcome::Failed(RuntimeError::InvalidState)
    ));
    assert_eq!(e.fuel(), fuel);
    // Reenter the same store with a distinct invocation while the first is waiting.
    let mut nested = Execution::new(&store, host, &[Value::I32(9)]).unwrap();
    nested.add_fuel(10).unwrap();
    assert!(matches!(nested.run(&mut store), Outcome::NeedsHostCall(_)));
    nested.resume_host(&store, Ok(&[Value::I32(10)])).unwrap();
    assert!(matches!(nested.run(&mut store), Outcome::Returned(_)));
    e.resume_host(&store, Ok(&[Value::I32(6)])).unwrap();
    assert_eq!(
        e.resume_host(&store, Ok(&[Value::I32(7)])),
        Err(RuntimeError::InvalidState)
    );
    match e.run(&mut store) {
        Outcome::Returned(v) => assert_eq!(v, [Value::I32(7)]),
        x => panic!("{x:?}"),
    }
}
#[test]
fn start_suspension_does_not_repeat_initialization() {
    let mut store = Store::new();
    let memory = store
        .define_memory(MemType {
            limits: Limits { min: 1, max: None },
        })
        .unwrap();
    let host = store
        .define_host(
            FuncType {
                params: vec![],
                results: vec![],
            },
            1,
        )
        .unwrap();
    let m = module(
        r#"(module (import "h" "m" (memory 1)) (import "h" "f" (func $host))
      (data (i32.const 0) "a") (func $start call $host i32.const 1 i32.const 2 i32.store8) (start $start))"#,
        ValidationProfile::Wasm2,
    );
    let mut init = store
        .instantiate(m, &[Extern::Memory(memory), Extern::Func(host)])
        .unwrap();
    assert!(init.instance().is_none());
    assert!(matches!(init.run(&mut store), Outcome::Suspended));
    assert_eq!(store.memory(memory).unwrap()[0], b'a');
    store.memory_mut(memory).unwrap()[0] = b'b';
    init.add_fuel(10).unwrap();
    assert!(matches!(init.run(&mut store), Outcome::NeedsHostCall(_)));
    init.resume_host(&store, Ok(&[])).unwrap();
    assert!(matches!(init.run(&mut store), Outcome::Returned(_)));
    assert_eq!(&store.memory(memory).unwrap()[..2], b"b\x02");
    assert!(init.instance().is_some());
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
            .define_memory(MemType {
                limits: Limits { min: 1, max: None },
            })
            .unwrap();
        assert!(matches!(
            store.instantiate(
                module(wat, profile),
                &[Extern::Table(table), Extern::Memory(memory)]
            ),
            Err(RuntimeError::Trap(Trap::MemoryOutOfBounds))
        ));
        if profile == ValidationProfile::Wasm1 {
            assert_eq!(store.memory(memory).unwrap()[0], 0);
            assert_eq!(store.table(table).unwrap()[0], Value::FuncRef(None));
        } else {
            assert_eq!(store.memory(memory).unwrap()[0], b'A');
            let f = match store.table(table).unwrap()[0] {
                Value::FuncRef(Some(f)) => f,
                _ => panic!(),
            };
            assert_eq!(run(&mut store, f, &[]), [Value::I32(77)]);
        }
    }
}
#[test]
fn wrong_store_and_foreign_references_are_rejected() {
    let mut a = Store::new();
    let b = Store::new();
    let f = a
        .define_host(
            FuncType {
                params: vec![],
                results: vec![],
            },
            0,
        )
        .unwrap();
    assert!(matches!(
        Execution::new(&b, f, &[]),
        Err(RuntimeError::WrongStore)
    ));
    let mut e = Execution::new(&a, f, &[]).unwrap();
    e.add_fuel(1).unwrap();
    let mut b = b;
    assert!(matches!(
        e.run(&mut b),
        Outcome::Failed(RuntimeError::WrongStore)
    ));
    assert!(matches!(e.run(&mut a), Outcome::NeedsHostCall(_)));
    let ext = a.define_extern(4).unwrap();
    assert!(matches!(
        b.define_global(
            GlobalType {
                mutability: Mut::Const,
                valtype: ValueType::ExternRef
            },
            Value::ExternRef(Some(ext))
        ),
        Err(RuntimeError::WrongStore)
    ));
}
#[test]
fn resource_limits_are_distinct_from_fuel_and_wasm_traps() {
    let mut store = Store::with_limits(StoreLimits {
        max_frames: 3,
        ..Default::default()
    });
    let i = instance(
        &mut store,
        r#"(module (func $f (export "f") call $f))"#,
        &[],
    );
    let mut e = Execution::new(&store, func(&store, i, "f"), &[]).unwrap();
    assert!(matches!(e.run(&mut store), Outcome::Suspended));
    e.add_fuel(100).unwrap();
    assert!(matches!(
        e.run(&mut store),
        Outcome::Failed(RuntimeError::Resource(ResourceLimit::CallStack))
    ));
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
    let mut e =
        Execution::new(&store, init, &[Value::I32(0), Value::I32(1), Value::I32(0)]).unwrap();
    e.add_fuel(100).unwrap();
    assert!(matches!(
        e.run(&mut store),
        Outcome::Failed(RuntimeError::Trap(Trap::MemoryOutOfBounds))
    ));
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
    let mut e = Execution::new(&store, f, &[]).unwrap();
    e.add_fuel(100).unwrap();
    assert!(matches!(
        e.run(&mut store),
        Outcome::Failed(RuntimeError::Trap(Trap::Unreachable))
    ));
    let m = match store.export(i, b"m").unwrap().unwrap() {
        Extern::Memory(m) => m,
        _ => panic!(),
    };
    assert_eq!(store.memory(m).unwrap()[0], 55);
}

#[test]
fn restart_reuses_completed_executions_and_preserves_failed_checks() {
    let mut store = Store::new();
    let i = instance(
        &mut store,
        r#"(module
      (func (export "fresh") (param i32) (result i32 i32) (local i32)
        local.get 1 local.get 0 local.set 1 local.get 1)
      (func (export "trap") (param i32) (result i32)
        local.get 0 i32.const 0 i32.div_u))"#,
        &[],
    );
    let fresh = func(&store, i, "fresh");
    let trap = func(&store, i, "trap");
    let mut e = Execution::new(&store, fresh, &[Value::I32(7)]).unwrap();
    assert_eq!(
        e.restart(&store, fresh, &[Value::I32(9)]),
        Err(RuntimeError::InvalidState)
    );
    assert!(matches!(e.run(&mut store), Outcome::Suspended));
    assert_eq!(
        e.restart(&store, fresh, &[Value::I32(9)]),
        Err(RuntimeError::InvalidState)
    );
    e.add_fuel(100).unwrap();
    let Outcome::Returned(first) = e.run(&mut store) else {
        panic!()
    };
    assert_eq!(first, [Value::I32(0), Value::I32(7)]);
    let fuel = e.fuel();
    assert_eq!(
        e.restart(&store, fresh, &[Value::I64(1)]),
        Err(RuntimeError::TypeMismatch)
    );
    assert_eq!(e.fuel(), fuel);
    let other = Store::new();
    assert_eq!(
        e.restart(&other, fresh, &[Value::I32(9)]),
        Err(RuntimeError::WrongStore)
    );
    e.restart(&store, trap, &[Value::I32(9)]).unwrap();
    assert_eq!(e.fuel(), 0);
    assert_eq!(e.source_offset(&store).unwrap(), None);
    e.add_fuel(100).unwrap();
    assert!(matches!(
        e.run(&mut store),
        Outcome::Failed(RuntimeError::Trap(Trap::IntegerDivideByZero))
    ));
    let offset = e.source_offset(&store).unwrap();
    let fuel = e.fuel();
    assert!(offset.is_some());
    assert_eq!(
        e.restart(&store, fresh, &[]),
        Err(RuntimeError::TypeMismatch)
    );
    assert_eq!(e.source_offset(&store).unwrap(), offset);
    assert_eq!(e.fuel(), fuel);
    // Restart after a trap clears the still-live frames, operands and locals.
    e.restart(&store, fresh, &[Value::I32(11)]).unwrap();
    e.add_fuel(100).unwrap();
    let Outcome::Returned(second) = e.run(&mut store) else {
        panic!()
    };
    assert_eq!(second, [Value::I32(0), Value::I32(11)]);
    assert_eq!(first, [Value::I32(0), Value::I32(7)]);
}

#[test]
fn restart_rejects_pending_host_and_rechecks_reference_ownership() {
    let mut store = Store::new();
    let host = store
        .define_host(
            FuncType {
                params: vec![ValueType::ExternRef],
                results: vec![ValueType::ExternRef],
            },
            7,
        )
        .unwrap();
    let mut e = Execution::new(&store, host, &[Value::ExternRef(None)]).unwrap();
    e.add_fuel(100).unwrap();
    assert!(matches!(e.run(&mut store), Outcome::NeedsHostCall(_)));
    assert_eq!(
        e.restart(&store, host, &[Value::ExternRef(None)]),
        Err(RuntimeError::InvalidState)
    );
    e.resume_host(&store, Err(RuntimeError::HostFailure))
        .unwrap();
    assert_eq!(
        e.restart(&store, host, &[Value::ExternRef(None)]),
        Err(RuntimeError::InvalidState)
    );
    assert!(matches!(
        e.run(&mut store),
        Outcome::Failed(RuntimeError::HostFailure)
    ));
    let mut other = Store::new();
    let foreign = other.define_extern(1).unwrap();
    assert_eq!(
        e.restart(&store, host, &[Value::ExternRef(Some(foreign))]),
        Err(RuntimeError::WrongStore)
    );
    let own = store.define_extern(2).unwrap();
    e.restart(&store, host, &[Value::ExternRef(Some(own))])
        .unwrap();
    e.add_fuel(100).unwrap();
    let Outcome::NeedsHostCall(request) = e.run(&mut store) else {
        panic!()
    };
    assert_eq!(request.arguments, [Value::ExternRef(Some(own))]);
    e.resume_host(&store, Ok(&request.arguments)).unwrap();
    let Outcome::Returned(values) = e.run(&mut store) else {
        panic!()
    };
    assert_eq!(values, [Value::ExternRef(Some(own))]);
}
