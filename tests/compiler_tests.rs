use itasca::{runtime::compile, ValidationProfile};

fn bytes(source: &str) -> Vec<u8> {
    let buffer = wast::parser::ParseBuffer::new(source).unwrap();
    wast::parser::parse::<wast::Wat>(&buffer)
        .unwrap()
        .encode()
        .unwrap()
}

#[test]
fn compilation_owns_metadata_and_checks_the_entire_tail() {
    let mut input = bytes(
        "(module (memory 1) (func (result i32) i32.const 5)
        (data (i32.const 0) \"hello\"))",
    );
    let module = compile(&input, ValidationProfile::Wasm1).unwrap();
    input.fill(0);
    assert_eq!(module.tail().data[0].init, b"hello");
    assert_eq!(module.function_count(), 1);
    assert_eq!(module.profile(), ValidationProfile::Wasm1);

    let mut invalid = bytes("(module (func))");
    invalid.extend_from_slice(&[11, 2, 1, 0]);
    assert!(compile(&invalid, ValidationProfile::Wasm1).is_err());
    assert!(compile(&invalid, ValidationProfile::Wasm2).is_err());
}

#[test]
fn source_coordinates_identify_original_opcodes_in_complete_module() {
    let input = bytes(
        "(module (func (param i32) (result i32) (local i64)
        local.get 0 if (result i32) i32.const 100 else i32.const 200 end))",
    );
    let module = compile(&input, ValidationProfile::Wasm2).unwrap();
    let stats = module.function_stats(0).unwrap();
    assert_eq!(stats.local_count, 2);
    assert_eq!(stats.max_stack, 1);
    let offsets = module.function_source_offsets(0).unwrap();
    let opcodes: Vec<_> = offsets.iter().map(|offset| input[*offset]).collect();
    assert_eq!(opcodes, [0x20, 0x04, 0x41, 0x05, 0x41, 0x0b]);
    assert_eq!(offsets[0], stats.body_start);
    assert_eq!(offsets[5] + 1, stats.body_end);
    let controls = module.function_control_map(0).unwrap();
    assert_eq!(controls[1].source_start, offsets[1]);
    assert_eq!(input[controls[1].source_end - 1], 0x0b);
    assert_eq!(controls[1].end_pc, 5);
}

#[test]
fn frame_payload_counts_both_vector_words() {
    let input = bytes("(module (func (param v128) (result v128) local.get 0))");
    let module = compile(&input, ValidationProfile::Wasm2).unwrap();
    let stats = module.function_stats(0).unwrap();
    assert_eq!(stats.local_count, 1);
    assert_eq!(stats.max_stack, 1);
    assert_eq!(stats.slot_count, 4);
}

#[test]
fn function_identity_survives_multiple_batches_and_reverse_retirement() {
    let mut text = String::from("(module (import \"m\" \"f\" (func))");
    for index in 0..6 {
        text.push_str("(func (result i32)");
        for _ in 0..26_000 {
            text.push_str(" nop");
        }
        text.push_str(&format!(" i32.const {index})"));
    }
    text.push(')');
    let input = bytes(&text);
    let module = compile(&input, ValidationProfile::Wasm2).unwrap();
    assert_eq!(module.function_count(), 6);
    assert_eq!(module.env().num_imported_funcs(), 1);
    for index in 0..6 {
        let stats = module.function_stats(index).unwrap();
        assert_eq!(stats.instruction_count, 2);
        let offsets = module.function_source_offsets(index).unwrap();
        assert_eq!(input[offsets[0]], 0x41);
        assert_eq!(input[offsets[0] + 1], index as u8);
        assert_eq!(offsets[1] + 1, stats.body_end);
    }
}

#[test]
fn profiles_and_unreachable_multivalue_branches_remain_distinct() {
    let input = bytes(
        "(module (func (result i32 i64)
        unreachable (block (result f32 f64)
            unreachable br_table 0 1) drop drop))",
    );
    assert!(compile(&input, ValidationProfile::Wasm1).is_err());
    let module = compile(&input, ValidationProfile::Wasm2).unwrap();
    assert_eq!(module.function_stats(0).unwrap().max_stack, 0);
}

#[test]
fn compiler_budgets_reject_partial_artifacts_with_explicit_resource_errors() {
    use itasca::runtime::{compile_with_limits, CompileError, CompileLimits, CompileResource};
    let input = bytes(
        "(module (func (param i32) (result i32)
        (block (result i32) i32.const 9 local.get 0 br_table 0 0)))",
    );
    let compiled = compile(&input, ValidationProfile::Wasm2).unwrap();
    // Branch copy/jump stubs count as emitted bytecode. Instantiation also
    // retains one synthetic return even when there are no active segments.
    let instruction_budget = compiled.function_stats(0).unwrap().instruction_count + 1;
    let enough = CompileLimits {
        max_module_bytes: input.len(),
        max_types: 1,
        max_functions: 1,
        max_instructions: instruction_budget,
        max_branch_table_entries: 2,
        max_controls: 2,
        max_locals: 1,
    };
    assert!(compile_with_limits(&input, ValidationProfile::Wasm2, enough).is_ok());
    for (limits, resource) in [
        (
            CompileLimits {
                max_module_bytes: input.len() - 1,
                ..enough
            },
            CompileResource::ModuleBytes,
        ),
        (
            CompileLimits {
                max_types: 0,
                ..enough
            },
            CompileResource::Types,
        ),
        (
            CompileLimits {
                max_functions: 0,
                ..enough
            },
            CompileResource::Functions,
        ),
        (
            CompileLimits {
                max_instructions: instruction_budget - 1,
                ..enough
            },
            CompileResource::Instructions,
        ),
        (
            CompileLimits {
                max_branch_table_entries: 1,
                ..enough
            },
            CompileResource::BranchTableEntries,
        ),
        (
            CompileLimits {
                max_controls: 1,
                ..enough
            },
            CompileResource::Controls,
        ),
        (
            CompileLimits {
                max_locals: 0,
                ..enough
            },
            CompileResource::Locals,
        ),
    ] {
        assert_eq!(
            compile_with_limits(&input, ValidationProfile::Wasm2, limits).unwrap_err(),
            CompileError::Resource(resource)
        );
    }
    let invalid = bytes("(module (func (result i32)))");
    assert!(matches!(
        compile_with_limits(&invalid, ValidationProfile::Wasm2, CompileLimits::default()),
        Err(CompileError::Validation(_))
    ));
}

#[test]
fn compiler_budgets_are_shared_across_defined_functions() {
    use itasca::runtime::{compile_with_limits, CompileError, CompileLimits, CompileResource};
    let input = bytes("(module (func nop) (func nop))");
    let limits = CompileLimits {
        max_instructions: 2,
        ..CompileLimits::default()
    };
    assert_eq!(
        compile_with_limits(&input, ValidationProfile::Wasm2, limits).unwrap_err(),
        CompileError::Resource(CompileResource::Instructions)
    );
    let limits = CompileLimits {
        max_controls: 1,
        ..CompileLimits::default()
    };
    assert_eq!(
        compile_with_limits(&input, ValidationProfile::Wasm2, limits).unwrap_err(),
        CompileError::Resource(CompileResource::Controls)
    );
}
