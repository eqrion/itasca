//! Regressions for embedding resource failures outside specification corpora.
use itasca::runtime::*;
use itasca::{FuncType, ValidationProfile, ValueType};

struct Hooks;
impl Platform<VecMemory> for Hooks {
    fn interrupt(&mut self) -> InterruptAction {
        InterruptAction::Continue
    }
    fn call_host(
        &mut self,
        _: &mut Store,
        _: u64,
        _: &[Value],
        _: &mut [Value],
    ) -> Result<(), HostError> {
        Err(HostError::Trap)
    }
}

fn module(text: &str) -> ExecutableModule {
    let buffer = wast::parser::ParseBuffer::new(text).unwrap();
    let mut ast = wast::parser::parse::<wast::Wat>(&buffer).unwrap();
    compile(&ast.encode().unwrap(), ValidationProfile::Wasm2).unwrap()
}
fn finish(store: &mut Store, code: ExecutableModule) -> InstanceAddr {
    store.instantiate(code, &[], &mut Hooks).unwrap()
}

fn function(store: &Store, instance: InstanceAddr, name: &[u8]) -> FuncAddr {
    match store.export(instance, name).unwrap().unwrap() {
        Extern::Func(f) => f,
        _ => panic!("expected function"),
    }
}
fn call(store: &mut Store, f: FuncAddr) -> Vec<Value> {
    let mut values = Vec::new();
    Execution::new()
        .invoke(store, &mut Hooks, f, &[], &mut values)
        .unwrap();
    values
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
        store.instantiate(failing, &[], &mut Hooks),
        Err(ExecError::Exhausted(ResourceLimit::Allocation))
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
            &[],
            &mut Hooks
        ),
        Err(ExecError::Exhausted(_))
    ));
    assert!(matches!(
        store.define_host(
            FuncType {
                params: vec![ValueType::I32; 4],
                results: vec![],
            },
            0
        ),
        Err(ExecError::Exhausted(_))
    ));
    let shared = module("(module (type (func (param i32 i32))))");
    finish(&mut store, module("(module (type (func (param i32 i32))))"));
    finish(&mut store, shared); // Canonically equal signatures share their budget.
    assert!(matches!(
        store.instantiate(
            module("(module (type (func (param i64 i64))))"),
            &[],
            &mut Hooks
        ),
        Err(ExecError::Exhausted(_))
    ));
    // A failed signature reservation did not consume the remaining one value.
    finish(&mut store, module("(module (type (func (result i64))))"));
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
        store.instantiate(failing, &[], &mut Hooks),
        Err(ExecError::Exhausted(ResourceLimit::Objects))
    ));
    store
        .define_memory(
            itasca::MemType {
                limits: itasca::Limits {
                    min: 1,
                    max: Some(1),
                },
            },
            VecMemory::new_zeroed(65536).unwrap(),
        )
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
