//! Regressions for embedding resource failures outside specification corpora.
use itasca::runtime::*;
use itasca::{FuncType, ValidationProfile, ValueType};
use std::rc::Rc;

fn module(text: &str) -> Rc<ExecutableModule> {
    let buffer = wast::parser::ParseBuffer::new(text).unwrap();
    let mut ast = wast::parser::parse::<wast::Wat>(&buffer).unwrap();
    Rc::new(compile(&ast.encode().unwrap(), ValidationProfile::Wasm2).unwrap())
}
fn finish(store: &mut Store, code: Rc<ExecutableModule>) -> InstanceAddr {
    let mut pending = store.instantiate(code, &[]).unwrap();
    pending.add_fuel(1000).unwrap();
    assert!(matches!(pending.run(store), Outcome::Returned(_)));
    pending.instance().unwrap()
}
fn function(store: &Store, instance: InstanceAddr, name: &[u8]) -> FuncAddr {
    match store.export(instance, name).unwrap().unwrap() {
        Extern::Func(f) => f,
        _ => panic!("expected function"),
    }
}
fn call(store: &mut Store, f: FuncAddr) -> Vec<Value> {
    let mut execution = Execution::new(store, f, &[]).unwrap();
    execution.add_fuel(1000).unwrap();
    match execution.run(store) {
        Outcome::Returned(values) => values,
        other => panic!("unexpected result: {other:?}"),
    }
}

#[test]
fn prepublication_allocation_failure_releases_unissued_addresses_and_budgets() {
    let mut store = Store::with_limits(StoreLimits {
        max_objects: 3, // One canonical type and two defined functions.
        max_memory_bytes: 0,
        ..Default::default()
    });
    let failing = module("(module (func (result i32) i32.const 99) (memory 1))");
    assert!(matches!(
        store.instantiate(failing, &[]),
        Err(RuntimeError::Resource(ResourceLimit::Allocation))
    ));
    let instance = finish(
        &mut store,
        module(
            r#"(module
        (func (export "first") (result i32) i32.const 17)
        (func (export "second") (result i32) i32.const 29))"#,
        ),
    );
    let first = function(&store, instance, b"first");
    let second = function(&store, instance, b"second");
    assert_eq!(call(&mut store, first), [Value::I32(17)]);
    assert_eq!(call(&mut store, second), [Value::I32(29)]);
}

#[test]
fn unused_and_host_signatures_obey_total_value_budget() {
    let mut store = Store::with_limits(StoreLimits {
        max_signature_values: 3,
        ..Default::default()
    });
    assert!(matches!(
        store.instantiate(
            module("(module (type (func (param i32 i32 i32 i32))))"),
            &[]
        ),
        Err(RuntimeError::Resource(_))
    ));
    assert!(matches!(
        store.define_host(
            FuncType {
                params: vec![ValueType::I32; 4],
                results: vec![],
            },
            0
        ),
        Err(RuntimeError::Resource(_))
    ));
    let shared = module("(module (type (func (param i32 i32))))");
    finish(&mut store, Rc::clone(&shared));
    finish(&mut store, shared); // Canonically equal signatures share their budget.
    assert!(matches!(
        store.instantiate(module("(module (type (func (param i64 i64))))"), &[]),
        Err(RuntimeError::Resource(_))
    ));
    // A failed signature reservation did not consume the remaining one value.
    finish(&mut store, module("(module (type (func (result i64))))"));
}

#[test]
fn suspended_indirect_call_resolves_current_table_and_recomputes_cost() {
    let mut store = Store::new();
    let instance = finish(
        &mut store,
        module(
            r#"(module
        (type $t (func (result i32)))
        (table (export "table") 1 funcref)
        (func $heavy (type $t) (local i32 i32 i32 i32 i32 i32 i32 i32)
          i32.const 99)
        (func $cheap (export "cheap") (type $t) i32.const 17)
        (elem (i32.const 0) $heavy)
        (func (export "indirect") (result i32) i32.const 0 call_indirect (type $t)))"#,
        ),
    );
    let indirect = function(&store, instance, b"indirect");
    let cheap = function(&store, instance, b"cheap");
    let table = match store.export(instance, b"table").unwrap().unwrap() {
        Extern::Table(t) => t,
        _ => panic!("expected table"),
    };
    let mut execution = Execution::new(&store, indirect, &[]).unwrap();
    execution.add_fuel(3).unwrap();
    // Initial call and i32.const consume two; the heavy call requires nine.
    assert!(matches!(execution.run(&mut store), Outcome::Suspended));
    assert_eq!(execution.fuel(), 1);
    store
        .set_table(table, 0, Value::FuncRef(Some(cheap)))
        .unwrap();
    // The retained one unit now suffices for the replacement call. Its operands
    // were preserved, and resumption does not retain the former target.
    assert!(matches!(execution.run(&mut store), Outcome::Suspended));
    assert_eq!(execution.fuel(), 0);
    execution.add_fuel(3).unwrap();
    match execution.run(&mut store) {
        Outcome::Returned(values) => assert_eq!(values, [Value::I32(17)]),
        other => panic!("unexpected result: {other:?}"),
    }
}

#[test]
fn provisional_failures_restore_aggregate_memory_and_table_budgets() {
    let mut store = Store::with_limits(StoreLimits {
        max_objects: 4,
        max_memory_bytes: 65536,
        max_table_elements: 1,
        ..Default::default()
    });
    let failing = module("(module (func) (table 1 funcref) (memory 1) (global i32 (i32.const 0)))");
    // Type + function + table + memory exhaust the object budget before the
    // global can be allocated. None of the provisional addresses can escape.
    assert!(matches!(
        store.instantiate(failing, &[]),
        Err(RuntimeError::Resource(ResourceLimit::Objects))
    ));
    store
        .define_memory(itasca::MemType {
            limits: itasca::Limits {
                min: 1,
                max: Some(1),
            },
        })
        .unwrap();
    store
        .define_table(itasca::TableType {
            elem: itasca::ElemType::FuncRef,
            limits: itasca::Limits {
                min: 1,
                max: Some(1),
            },
        })
        .unwrap();
}
