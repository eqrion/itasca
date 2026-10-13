#![allow(dead_code)]
use crate::differential::{Coverage, Pair};
use itasca::{runtime::Value, ValidationProfile};

fn wat(source: &str) -> Vec<u8> {
    let buffer = wast::parser::ParseBuffer::new(source).unwrap();
    wast::parser::parse::<wast::Wat>(&buffer)
        .unwrap()
        .encode()
        .unwrap()
}

pub fn stateful(data: &[u8]) -> Coverage {
    let provider = wat(r#"(module
      (import "host" "trace" (func $trace (param i32)))
      (memory (export "memory") 1 2)
      (table (export "table") 4 16 funcref)
      (global $g (export "global") (mut i32) (i32.const 0))
      (func (export "bump") (param i32) (result i32)
        global.get $g local.get 0 i32.add global.set $g
        global.get $g call $trace global.get $g))"#);
    let consumer = wat(r#"(module
      (import "p" "memory" (memory 1 2))
      (import "p" "table" (table 4 16 funcref))
      (import "p" "bump" (func $bump (param i32) (result i32)))
      (data $d "hello world")
      (elem (i32.const 0) $entry)
      (func $entry (export "step") (param i32 i32) (result i32)
        local.get 0 local.get 1 call $bump i32.store
        local.get 0 i32.load)
      (func (export "trap") (param i32 i32)
        local.get 0 local.get 1 i32.store unreachable)
      (func (export "grow") (param i32) (result i32) local.get 0 memory.grow)
      (func (export "table-grow") (param i32) (result i32) ref.null func local.get 0 table.grow)
      (func (export "init") (param i32 i32 i32)
        local.get 0 local.get 1 local.get 2 memory.init $d)
      (func (export "copy") (param i32 i32 i32)
        local.get 0 local.get 1 local.get 2 memory.copy)
      (func (export "fill") (param i32 i32 i32)
        local.get 0 local.get 1 local.get 2 memory.fill)
      (func (export "table-fill") (param i32 i32)
        local.get 0 ref.null func local.get 1 table.fill)
      (func (export "drop") data.drop $d))"#);
    let mut pair = Pair::new(ValidationProfile::Wasm2);
    for (bytes, provider) in [(&provider, None), (&consumer, Some(0))] {
        let status = pair.instantiate(bytes, ValidationProfile::Wasm2, provider);
        if status != Coverage::Compared {
            return status;
        }
    }
    for action in data.chunks(4).take(32) {
        let number = |i| Value::I32(action.get(i).copied().unwrap_or(0) as u32);
        let (name, args) = match action[0] % 9 {
            0 => ("step", vec![number(1), number(2)]),
            1 => ("trap", vec![number(1), number(2)]),
            2 => ("grow", vec![number(1)]),
            3 => ("table-grow", vec![number(1)]),
            4 => ("init", vec![number(1), number(2), number(3)]),
            5 => ("copy", vec![number(1), number(2), number(3)]),
            6 => ("fill", vec![number(1), number(2), number(3)]),
            7 => ("table-fill", vec![number(1), number(2)]),
            _ => ("drop", vec![]),
        };
        let status = pair.call(1, name, &args);
        if status != Coverage::Compared {
            return status;
        }
    }
    Coverage::Compared
}

pub fn linking(data: &[u8]) -> Coverage {
    let seed = data.first().copied().unwrap_or(0);
    let provider = wat(r#"(module
      (memory (export "memory") 1 2)
      (table (export "table") 4 16 funcref)
      (global (export "global") (mut i32) (i32.const 7))
      (func (export "function") (param i32) (result i32) local.get 0))"#);
    let source = match seed % 7 {
        0 => "(module (import \"p\" \"memory\" (memory 3)))".to_string(),
        1 => "(module (import \"p\" \"table\" (table 4 8 funcref)))".to_string(),
        2 => "(module (import \"p\" \"global\" (global i32)))".to_string(),
        3 => "(module (import \"p\" \"function\" (func (param i64))))".to_string(),
        4 => "(module (import \"p\" \"function\" (memory 1)))".to_string(),
        5 => format!(
            r#"(module (import "p" "memory" (memory 1 2))
          (data (i32.const 0) "first") (data (i32.const {}) "last"))"#,
            if data.get(1).copied().unwrap_or(0) % 2 == 0 {
                65535
            } else {
                100
            }
        ),
        _ => format!(
            r#"(module (import "p" "memory" (memory 1 2))
          (data (i32.const 0) "first")
          (func $start i32.const 16 i32.const {} i32.store unreachable) (start $start))"#,
            data.get(1).copied().unwrap_or(0)
        ),
    };
    let consumer = wat(&source);
    let mut pair = Pair::new(ValidationProfile::Wasm2);
    let status = pair.instantiate(&provider, ValidationProfile::Wasm2, None);
    if status != Coverage::Compared {
        return status;
    }
    pair.instantiate(&consumer, ValidationProfile::Wasm2, Some(0))
}
