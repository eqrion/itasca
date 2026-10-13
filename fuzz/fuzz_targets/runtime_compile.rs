#![no_main]
#[path = "../../tests/support/runtime_differential.rs"]
mod differential;
#[path = "../../tests/support/mvp_binary.rs"]
mod mvp_binary;

libfuzzer_sys::fuzz_target!(|data: &[u8]| {
    let Some((&which, bytes)) = data.split_first() else {
        differential::record(differential::Coverage::Invalid);
        return;
    };
    let profile = if which % 2 == 0 {
        itasca::ValidationProfile::Wasm1
    } else {
        itasca::ValidationProfile::Wasm2
    };
    let Ok(module) = itasca::runtime::compile(bytes, profile) else {
        differential::record(differential::Coverage::Invalid);
        return;
    };
    // Arbitrary programs have no per-operation NaN canonicalization. Compile
    // all of them; strictly execute the integer/reference subset here.
    let mut numeric = false;
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        if let wasmparser::Payload::CodeSectionEntry(body) =
            payload.expect("accepted bytes parse independently")
        {
            let mut ops = body
                .get_operators_reader()
                .expect("accepted function body parses independently");
            while !ops.eof() {
                let op = ops.read().expect("accepted operator parses independently");
                let name = format!("{op:?}");
                numeric |= name.starts_with("F32")
                    || name.starts_with("F64")
                    || name.starts_with("V128")
                    || name.contains("x2")
                    || name.contains("x4")
                    || name.contains("x8")
                    || name.contains("x16");
            }
        }
    }
    if numeric || module.env().mem_types().len() > 1 {
        differential::record(differential::Coverage::NumericNondeterminism);
        return;
    }
    differential::record(differential::compare(bytes, profile, data));
});
