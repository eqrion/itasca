use arbitrary::Unstructured;
use wasm_smith::{Config, Module};

pub fn run(data: &[u8]) -> crate::differential::Coverage {
    let config = Config {
        bulk_memory_enabled: true,
        reference_types_enabled: true,
        simd_enabled: true,
        multi_value_enabled: true,
        saturating_float_to_int_enabled: true,
        sign_extension_ops_enabled: true,
        relaxed_simd_enabled: false,
        exceptions_enabled: false,
        memory64_enabled: false,
        tail_call_enabled: false,
        threads_enabled: false,
        shared_everything_threads_enabled: false,
        gc_enabled: false,
        custom_descriptors_enabled: false,
        custom_page_sizes_enabled: false,
        wide_arithmetic_enabled: false,
        extended_const_enabled: false,
        canonicalize_nans: true,
        export_everything: true,
        allow_start_export: false,
        min_funcs: 1,
        max_funcs: 8,
        max_types: 8,
        max_type_size: 16,
        max_globals: 8,
        max_imports: 8,
        max_exports: 16,
        max_tables: if true { 4 } else { 1 },
        max_memories: 1,
        max_memory32_bytes: 16 * 65536,
        memory_max_size_required: true,
        max_table_elements: 64,
        table_max_size_required: true,
        max_data_segments: 8,
        max_element_segments: 8,
        max_elements: 16,
        max_instructions: 64,
        ..Config::default()
    };
    let Ok(mut module) = Module::new(config, &mut Unstructured::new(data)) else {
        crate::differential::record(crate::differential::Coverage::Invalid);
        return crate::differential::Coverage::Invalid;
    };
    // Both engines execute the same source-level termination guard. The
    // interpreter interrupt limit is an infrastructure backstop. Wasmi runs without fuel.
    module.ensure_termination(100).unwrap();
    let bytes = module.to_bytes();
    let status = crate::differential::compare(&bytes, data);
    assert_ne!(
        status,
        crate::differential::Coverage::Invalid,
        "generated module was rejected: bytes={bytes:?}"
    );
    crate::differential::record(status);
    status
}
