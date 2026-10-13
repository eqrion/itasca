//! Fuel partitioning must preserve results, state, and host-call order.
use itasca::runtime::*;
use itasca::{FuncType, ValidationProfile, ValueType};
use std::rc::Rc;

#[derive(Debug, PartialEq, Eq)]
struct Observation {
    result: Vec<Value>,
    memory: Vec<u8>,
    table: Vec<u8>,
    global: Value,
    host_trace: Vec<Vec<Value>>,
    fuel_used: u64,
}

fn observe(slices: &[u64], n: u32) -> Observation {
    let text = r#"(module
      (import "h" "step" (func $host (param i32) (result i32)))
      (memory (export "memory") 1 2)
      (table (export "table") 3 8 funcref)
      (global $total (export "total") (mut i32) (i32.const 0))
      (func $f (export "f")) (func $g (export "g"))
      (elem $elements func $f $g)
      (data $bytes "abcdef")
      (func (export "run") (param $n i32) (result i32) (local $i i32)
        i32.const 1 memory.grow drop
        i32.const 0 i32.const 0 i32.const 6 memory.init $bytes
        data.drop $bytes
        i32.const 0 i32.const 0 i32.const 2 table.init $elements
        elem.drop $elements
        ref.func $f i32.const 1 table.grow drop
        i32.const 1 i32.const 0 i32.const 2 table.copy
        block $done
          loop $loop
            local.get $i local.get $n i32.ge_u br_if $done
            local.get $i call $host
            global.get $total i32.add global.set $total
            local.get $i i32.const 1 i32.add local.set $i
            br $loop
          end
        end
        i32.const 32 global.get $total i32.const 129 memory.fill
        global.get $total))"#;
    let buffer = wast::parser::ParseBuffer::new(text).unwrap();
    let mut wat = wast::parser::parse::<wast::Wat>(&buffer).unwrap();
    let code = Rc::new(compile(&wat.encode().unwrap(), ValidationProfile::Wasm2).unwrap());
    let mut store = Store::new();
    let host = store
        .define_host(
            FuncType {
                params: vec![ValueType::I32],
                results: vec![ValueType::I32],
            },
            7,
        )
        .unwrap();
    let mut pending = store.instantiate(code, &[Extern::Func(host)]).unwrap();
    assert!(matches!(pending.run(&mut store), Outcome::Returned(_)));
    let instance = pending.instance().unwrap();
    let export = |name: &[u8]| store.export(instance, name).unwrap().unwrap();
    let Extern::Func(run) = export(b"run") else {
        panic!()
    };
    let Extern::Func(f) = export(b"f") else {
        panic!()
    };
    let Extern::Func(g) = export(b"g") else {
        panic!()
    };
    let Extern::Memory(memory) = export(b"memory") else {
        panic!()
    };
    let Extern::Table(table) = export(b"table") else {
        panic!()
    };
    let Extern::Global(global) = export(b"total") else {
        panic!()
    };
    let mut execution = Execution::new(&store, run, &[Value::I32(n)]).unwrap();
    let mut supplied = 0;
    let mut slice = 0;
    let mut trace = Vec::new();
    let result = loop {
        match execution.run(&mut store) {
            Outcome::Suspended => {
                let amount = slices[slice % slices.len()];
                slice += 1;
                supplied += amount;
                assert!(supplied <= 2_000_000, "unexpected nontermination");
                execution.add_fuel(amount).unwrap();
            }
            Outcome::NeedsHostCall(request) => {
                assert_eq!(request.host_id, 7);
                let Value::I32(x) = request.arguments[0] else {
                    panic!()
                };
                trace.push(request.arguments);
                execution
                    .resume_host(&store, Ok(&[Value::I32(x + 1)]))
                    .unwrap();
            }
            Outcome::Returned(values) => break values,
            other => panic!("{other:?}"),
        }
    };
    let table = store
        .table(table)
        .unwrap()
        .iter()
        .map(|value| match value {
            Value::FuncRef(None) => 0,
            Value::FuncRef(Some(a)) if *a == f => 1,
            Value::FuncRef(Some(a)) if *a == g => 2,
            _ => panic!("unexpected reference"),
        })
        .collect();
    Observation {
        result,
        memory: store.memory(memory).unwrap().to_vec(),
        table,
        global: store.global(global).unwrap(),
        host_trace: trace,
        fuel_used: supplied - execution.fuel(),
    }
}

#[test]
fn arbitrary_fuel_partitions_preserve_all_observations_and_charges() {
    for n in [0, 1, 7, 31] {
        let uninterrupted = observe(&[1_000_000], n);
        for slices in [&[1][..], &[2, 3, 5, 7][..], &[64, 1, 1024, 4][..]] {
            assert_eq!(observe(slices, n), uninterrupted, "n={n} slices={slices:?}");
        }
    }
}
