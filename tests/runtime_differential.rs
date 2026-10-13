#[path = "support/runtime_differential.rs"]
mod differential;
#[path = "support/mvp_binary.rs"]
mod mvp_binary;
#[path = "support/runtime_numeric.rs"]
mod numeric;
#[path = "support/runtime_scenarios.rs"]
mod scenarios;
#[path = "../fuzz/fuzz_targets/runtime_smith_support.rs"]
mod smith;

use differential::{Coverage, Pair};
use itasca::runtime::Value;
use itasca::ValidationProfile;

fn wat(text: &str) -> Vec<u8> {
    let buffer = wast::parser::ParseBuffer::new(text).unwrap();
    wast::parser::parse::<wast::Wat>(&buffer)
        .unwrap()
        .encode()
        .unwrap()
}

#[test]
fn scalar_and_simd_differential() {
    let mut coverage = 0;
    for selector in 0..768u32 {
        let mut input = vec![0u8; 96];
        input[0] = (selector / 256) as u8;
        input[1] = (selector % 256) as u8;
        let mut state = selector as u64 + 1;
        for byte in &mut input[4..] {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            *byte = (state >> 32) as u8;
        }
        let (bytes, profile) = numeric::module(&input);
        assert_eq!(
            differential::compare(&bytes, profile, &input),
            Coverage::Compared,
            "selector {selector}"
        );
        coverage += 1;
    }
    assert_eq!(coverage, 768);
}

#[test]
fn numeric_ieee_edge_patterns() {
    // Raw values reach conversion/comparison/bit-selection operators. Arithmetic
    // operators deliberately receive bounded finite versions of these seeds.
    let patterns = [
        0,
        u64::MAX,
        0x8000_0000_8000_0000,
        0x7f80_0001_7fc0_0000,
        0x7ff0_0000_0000_0000,
        0x7ff0_0000_0000_0001,
        0x43e0_0000_0000_0000,
        0xc3e0_0000_0000_0000,
    ];
    for profile in [1u8, 2] {
        for op in 0..256u32 {
            for pattern in patterns {
                let mut input = vec![profile, op as u8];
                for _ in 0..12 {
                    input.extend_from_slice(&pattern.to_le_bytes());
                }
                let (bytes, profile) = numeric::module(&input);
                assert_eq!(
                    differential::compare(&bytes, profile, &input),
                    Coverage::Compared,
                    "profile {profile:?}, selector {op}, bits {pattern:016x}"
                );
            }
        }
    }
}

#[test]
fn stateful_cross_instance_and_host_effects() {
    let provider = wat(r#"(module
        (import "host" "trace" (func $trace (param i32)))
        (memory (export "memory") 1 2)
        (global $g (export "global") (mut i32) (i32.const 0))
        (func (export "bump") (param i32) (result i32)
          global.get $g local.get 0 i32.add global.set $g
          global.get $g call $trace global.get $g))"#);
    let consumer = wat(r#"(module
        (import "provider" "memory" (memory 1 2))
        (import "provider" "bump" (func $bump (param i32) (result i32)))
        (data (i32.const 4) "abc")
        (func (export "write") (param i32) (result i32)
          i32.const 0 local.get 0 call $bump i32.store i32.const 0 i32.load)
        (func (export "trap") i32.const 12 i32.const 99 i32.store unreachable)
        (func (export "grow") (result i32) i32.const 1 memory.grow))"#);
    let mut pair = Pair::new(ValidationProfile::Wasm2);
    assert_eq!(
        pair.instantiate(&provider, ValidationProfile::Wasm2, None),
        Coverage::Compared
    );
    assert_eq!(
        pair.instantiate(&consumer, ValidationProfile::Wasm2, Some(0)),
        Coverage::Compared
    );
    for value in [0, 1, u32::MAX, 42] {
        assert_eq!(
            pair.call(1, "write", &[Value::I32(value)]),
            Coverage::Compared
        );
        assert_eq!(pair.call(1, "trap", &[]), Coverage::Compared);
    }
    assert_eq!(pair.call(1, "grow", &[]), Coverage::Compared);
    assert_eq!(pair.call(1, "grow", &[]), Coverage::Compared);
}

#[test]
fn failed_instantiation_keeps_prior_shared_effects() {
    let provider = wat(r#"(module (memory (export "memory") 1))"#);
    let failing = wat(r#"(module (import "p" "memory" (memory 1))
        (data (i32.const 0) "abc") (data (i32.const 65536) "x"))"#);
    let mut pair = Pair::new(ValidationProfile::Wasm2);
    assert_eq!(
        pair.instantiate(&provider, ValidationProfile::Wasm2, None),
        Coverage::Compared
    );
    assert_eq!(
        pair.instantiate(&failing, ValidationProfile::Wasm2, Some(0)),
        Coverage::Compared
    );
    let mut old = Pair::new(ValidationProfile::Wasm1);
    assert_eq!(
        old.instantiate(&provider, ValidationProfile::Wasm1, None),
        Coverage::Compared
    );
    assert_eq!(
        old.instantiate(&failing, ValidationProfile::Wasm1, Some(0)),
        Coverage::ProfileDifference
    );
}

#[test]
fn stateful_and_linking_sequences() {
    for seed in 0..64u8 {
        let data: Vec<_> = (0..128u8)
            .map(|i| i.wrapping_mul(37).wrapping_add(seed))
            .collect();
        assert_eq!(
            scenarios::stateful(&data),
            Coverage::Compared,
            "stateful seed {seed}"
        );
        assert_eq!(
            scenarios::linking(&data),
            Coverage::Compared,
            "linking seed {seed}"
        );
    }
}

#[test]
fn bounded_generated_execution_both_profiles() {
    let mut compared = 0;
    let mut excluded = [0usize; 6];
    for seed in 0..128u64 {
        let mut state = seed + 1;
        let data: Vec<_> = (0..4096)
            .map(|_| {
                state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
                (state >> 32) as u8
            })
            .collect();
        for profile in [ValidationProfile::Wasm1, ValidationProfile::Wasm2] {
            let status = smith::run(&data, profile);
            excluded[status as usize] += 1;
            if status == Coverage::Compared {
                compared += 1;
            }
        }
    }
    eprintln!("generated execution coverage [compared,invalid,resource,profile,reference,numeric]={excluded:?}");
    assert!(
        compared >= 96,
        "excessive generated-module exclusions: {excluded:?}"
    );
}

#[test]
fn oracle_adapter_preserves_duplicate_names_and_mutable_globals() {
    let duplicate = wat(r#"(module
      (import "" "" (memory 0 7))
      (import "" "" (table 18 33 externref)))"#);
    assert_eq!(
        differential::compare(&duplicate, ValidationProfile::Wasm2, &[]),
        Coverage::Compared
    );
    let mutable = wat(r#"(module
      (global (export "g") (mut i32) (i32.const 1)))"#);
    assert_eq!(
        differential::compare(&mutable, ValidationProfile::Wasm1, &[]),
        Coverage::Compared
    );
}
