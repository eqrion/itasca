//! Repeated runtime comparisons; run in release mode with `--help` for options.
use itasca::runtime::{
    compile, Execution, Extern, FuncAddr, HostError, InterruptAction, Platform, Store, Value,
    VecMemory,
};
use itasca::ValidationProfile;
use std::{
    fs::File,
    hint::black_box,
    io::{BufWriter, Write},
    time::{Duration, Instant},
};

const MAX_REPEATS: usize = 1_000_000;

struct Options {
    samples: usize,
    sample_time: Duration,
    filter: String,
    csv: Option<BufWriter<File>>,
}

impl Options {
    fn parse() -> Self {
        let mut options = Self {
            samples: 9,
            sample_time: Duration::from_millis(50),
            filter: String::new(),
            csv: None,
        };
        let mut args = std::env::args().skip(1);
        while let Some(arg) = args.next() {
            if arg == "--help" {
                println!(
                    "runtime_bench [--samples N] [--sample-ms N] [--filter NAME] [--csv PATH]"
                );
                println!("Defaults: 9 samples, target 50 ms per sample, all workloads. Times include object/result cleanup.");
                std::process::exit(0);
            }
            let value = args.next().expect("option requires a value; use --help");
            match arg.as_str() {
                "--samples" => options.samples = value.parse().expect("positive sample count"),
                "--sample-ms" => {
                    options.sample_time =
                        Duration::from_millis(value.parse().expect("milliseconds"))
                }
                "--filter" => options.filter = value,
                "--csv" => options.csv = Some(BufWriter::new(File::create(value).unwrap())),
                _ => panic!("unknown option {arg}; use --help"),
            }
        }
        assert!(options.samples > 0 && options.samples <= 1000);
        assert!(!options.sample_time.is_zero());
        assert!(options.sample_time <= Duration::from_secs(60));
        options
    }
}

struct Case {
    name: &'static str,
    profile: ValidationProfile,
    text: String,
    argument: i32,
    expected: i32,
    provider: Option<String>,
}

fn cases() -> Vec<Case> {
    let mut cases = Vec::new();
    let mut add = |name, profile, text: &str, argument, expected| {
        cases.push(Case {
            name,
            profile,
            text: text.into(),
            argument,
            expected,
            provider: None,
        });
    };
    add(
        "call_boundary",
        ValidationProfile::Wasm1,
        r#"(module (func (export "run") (param i32) (result i32) local.get 0))"#,
        10000,
        10000,
    );
    add(
        "integer_loop",
        ValidationProfile::Wasm1,
        r#"(module (func (export "run") (param $n i32) (result i32) (local $sum i32)
        loop $loop
          local.get $sum local.get $n i32.add local.set $sum
          local.get $n i32.const 1 i32.sub local.tee $n br_if $loop
        end local.get $sum))"#,
        10000,
        50_005_000,
    );
    let direct = r#"(module
      (type $unary (func (param i32) (result i32)))
      (func $inc (type $unary) local.get 0 i32.const 1 i32.add)
      (func (export "run") (param $n i32) (result i32) (local $sum i32)
        loop $loop
          local.get $sum local.get $n call $inc i32.add local.set $sum
          local.get $n i32.const 1 i32.sub local.tee $n br_if $loop
        end local.get $sum))"#;
    add(
        "direct_calls",
        ValidationProfile::Wasm1,
        direct,
        10000,
        50_015_000,
    );
    let indirect = direct
        .replace(
            "(func $inc",
            "(table 1 funcref) (elem (i32.const 0) $inc) (func $inc",
        )
        .replace("call $inc", "i32.const 0 call_indirect (type $unary)");
    add(
        "indirect_calls",
        ValidationProfile::Wasm1,
        &indirect,
        10000,
        50_015_000,
    );
    add(
        "float_loop",
        ValidationProfile::Wasm1,
        r#"(module (func (export "run") (param $n i32) (result i32) (local $sum f64)
        loop $loop
          local.get $sum f64.const 0.5 f64.add local.set $sum
          local.get $n i32.const 1 i32.sub local.tee $n br_if $loop
        end local.get $sum i32.trunc_f64_s))"#,
        10000,
        5000,
    );
    let memory = format!(
        r#"(module (memory 1) (data (i32.const 0) "{}")
      (func (export "run") (param $n i32) (result i32) (local $sum i32)
        loop $loop
          local.get $n i32.const 1 i32.sub local.set $n
          local.get $sum local.get $n i32.const 4 i32.mul i32.load i32.add local.set $sum
          local.get $n br_if $loop
        end local.get $sum))"#,
        "\\01".repeat(65536)
    );
    add(
        "memory_sum_64k",
        ValidationProfile::Wasm1,
        &memory,
        16384,
        0x01010101u32.wrapping_mul(16384) as i32,
    );
    add(
        "bulk_copy_8m",
        ValidationProfile::Wasm2,
        r#"(module (memory 2)
      (func (export "run") (param $n i32) (result i32)
        i32.const 0 i32.const 90 i32.const 65536 memory.fill
        loop $loop
          i32.const 65536 i32.const 0 i32.const 65536 memory.copy
          local.get $n i32.const 1 i32.sub local.tee $n br_if $loop
        end i32.const 65536 i32.load))"#,
        128,
        0x5a5a5a5a,
    );
    add(
        "simd_loop",
        ValidationProfile::Wasm2,
        r#"(module (func (export "run") (param $n i32) (result i32) (local $sum v128)
        loop $loop
          local.get $sum v128.const i32x4 1 2 3 4 i32x4.add local.set $sum
          local.get $n i32.const 1 i32.sub local.tee $n br_if $loop
        end local.get $sum i32x4.extract_lane 3))"#,
        10000,
        40000,
    );
    let mut many = String::from("(module");
    for index in 0..128 {
        many.push_str(&format!(
            "(func $f{index} (param i32) (result i32) local.get 0 {} )",
            "i32.const 1 i32.add ".repeat(32)
        ));
    }
    many.push_str("(func (export \"run\") (param i32) (result i32) local.get 0 call $f127))");
    add(
        "many_functions",
        ValidationProfile::Wasm1,
        &many,
        10000,
        10032,
    );
    add(
        "unary_conversion",
        ValidationProfile::Wasm2,
        r#"(module (func (export "run") (param $n i32) (result i32) (local $sum i32)
        loop $loop
          local.get $sum local.get $n i64.extend_i32_u i64.clz i32.wrap_i64
          f64.convert_i32_u f64.neg f64.abs i32.trunc_f64_u i32.add local.set $sum
          local.get $n i32.const 1 i32.sub local.tee $n br_if $loop
        end local.get $sum))"#,
        10000,
        (1u64..=10000).map(|n| n.leading_zeros() as i32).sum(),
    );
    add(
        "memory_widths",
        ValidationProfile::Wasm1,
        r#"(module (memory 1)
        (func (export "run") (param $n i32) (result i32) (local $sum i32)
        loop $loop
          i32.const 1 local.get $n i32.store8
          i32.const 3 local.get $n i32.store16
          i32.const 7 local.get $n i32.store
          i32.const 13 local.get $n i64.extend_i32_u i64.store
          local.get $sum i32.const 1 i32.load8_u i32.add
          i32.const 3 i32.load16_u i32.add i32.const 7 i32.load i32.add
          i32.const 13 i64.load i32.wrap_i64 i32.add local.set $sum
          local.get $n i32.const 1 i32.sub local.tee $n br_if $loop
        end local.get $sum))"#,
        10000,
        (1..=10000).map(|n| (n & 255) + 3 * n).sum(),
    );
    add(
        "recursive_calls",
        ValidationProfile::Wasm1,
        r#"(module (func $recur (export "run") (param $n i32) (result i32)
          local.get $n i32.eqz if (result i32) i32.const 0 else
            local.get $n local.get $n i32.const 1 i32.sub call $recur i32.add
          end))"#,
        128,
        8256,
    );
    let mixed = format!(
        r#"(module (memory 1) (func (export "run") (param i32) (result i32)
        local.get 0 {}))"#,
        "i32.const 1 i32.add i64.extend_i32_u i64.const 3 i64.xor i32.wrap_i64 \
         f64.convert_i32_u f64.const 0.5 f64.add i32.trunc_f64_u \
         local.tee 0 i32.const 7 local.get 0 i32.store i32.const 7 i32.load i32.xor \
         local.get 0 i32.add "
            .repeat(1024)
    );
    let mut expected = 10000;
    for _ in 0..1024 {
        expected = (expected + 1) ^ 3;
    }
    add(
        "large_mixed_body",
        ValidationProfile::Wasm1,
        &mixed,
        10000,
        expected,
    );
    cases.push(Case {
        name: "cross_instance",
        profile: ValidationProfile::Wasm1,
        text: direct.replace(
            "(func $inc (type $unary) local.get 0 i32.const 1 i32.add)",
            "(import \"provider\" \"inc\" (func $inc (type $unary)))",
        ),
        argument: 10000,
        expected: 50_015_000,
        provider: Some(
            r#"(module (global i32 (i32.const 1))
            (func (export "inc") (param i32) (result i32) local.get 0 global.get 0 i32.add))"#
                .into(),
        ),
    });
    cases
}

fn oracle_engine(profile: ValidationProfile) -> wasmi::Engine {
    let wasm2 = profile == ValidationProfile::Wasm2;
    let mut config = wasmi::Config::default();
    config
        .compilation_mode(wasmi::CompilationMode::Eager)
        .wasm_mutable_global(true)
        .wasm_sign_extension(wasm2)
        .wasm_saturating_float_to_int(wasm2)
        .wasm_multi_value(wasm2)
        .wasm_bulk_memory(wasm2)
        .wasm_reference_types(wasm2)
        .wasm_simd(wasm2)
        .wasm_multi_memory(false)
        .wasm_tail_call(false)
        .wasm_extended_const(false)
        .wasm_custom_page_sizes(false)
        .wasm_wide_arithmetic(false)
        .wasm_relaxed_simd(false);
    wasmi::Engine::new(&config)
}

struct BenchPlatform;
impl Platform<VecMemory> for BenchPlatform {
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
fn our_instance(
    bytes: &[u8],
    provider: Option<&[u8]>,
    profile: ValidationProfile,
) -> (Store, FuncAddr) {
    let mut store = Store::new();
    let mut imports = Vec::new();
    if let Some(provider) = provider {
        let instance = store
            .instantiate(compile(provider, profile).unwrap(), &[], &mut BenchPlatform)
            .unwrap()
            .instance;
        imports.push(store.export(instance, b"inc").unwrap().unwrap());
    }
    let instance = store
        .instantiate(
            compile(bytes, profile).unwrap(),
            &imports,
            &mut BenchPlatform,
        )
        .unwrap()
        .instance;
    let Some(Extern::Func(function)) = store.export(instance, b"run").unwrap() else {
        panic!("missing run export")
    };
    (store, function)
}
fn our_call(
    store: &mut Store,
    function: FuncAddr,
    argument: i32,
    inspect: impl FnOnce(&Execution),
) -> i32 {
    let mut execution = Execution::new();
    let result = our_reused_call(store, &mut execution, function, argument);
    inspect(&execution);
    result
}
fn our_reused_call(
    store: &mut Store,
    execution: &mut Execution,
    function: FuncAddr,
    argument: i32,
) -> i32 {
    let mut values = Vec::new();
    execution
        .invoke(
            store,
            &mut BenchPlatform,
            function,
            &[Value::I32(argument as u32)],
            &mut values,
        )
        .unwrap();
    let [Value::I32(result)] = values.as_slice() else {
        panic!("unexpected result type")
    };
    *result as i32
}

fn oracle_instance(
    engine: &wasmi::Engine,
    code: &wasmi::Module,
    provider: Option<&wasmi::Module>,
) -> (wasmi::Store<()>, wasmi::Func) {
    let mut store = wasmi::Store::new(engine, ());
    let mut imports = Vec::new();
    if let Some(provider) = provider {
        let instance = wasmi::Instance::new(&mut store, provider, &[]).unwrap();
        imports.push(wasmi::Extern::Func(
            instance.get_func(&store, "inc").unwrap(),
        ));
    }
    let instance = wasmi::Instance::new(&mut store, code, &imports).unwrap();
    let function = instance.get_func(&store, "run").unwrap();
    (store, function)
}

fn oracle_call(store: &mut wasmi::Store<()>, function: wasmi::Func, argument: i32) -> i32 {
    let mut result = [wasmi::Val::I32(0)];
    function
        .call(store, &[wasmi::Val::I32(argument)], &mut result)
        .unwrap();
    result[0].i32().unwrap()
}

fn time_batch(f: &mut impl FnMut(), repeats: usize) -> Duration {
    let start = Instant::now();
    for _ in 0..repeats {
        f();
    }
    start.elapsed()
}

fn calibrate(f: &mut impl FnMut(), target: Duration) -> usize {
    let mut repeats = 1;
    loop {
        let elapsed = time_batch(f, repeats);
        if elapsed >= target || repeats == MAX_REPEATS {
            return repeats;
        }
        let factor = (target.as_secs_f64() / elapsed.as_secs_f64().max(1e-9))
            .ceil()
            .clamp(2.0, 16.0) as usize;
        repeats = repeats.saturating_mul(factor).min(MAX_REPEATS);
    }
}

fn summary(samples: &[f64]) -> (f64, f64, f64) {
    let mut sorted = samples.to_vec();
    sorted.sort_by(f64::total_cmp);
    let median = (sorted[(sorted.len() - 1) / 2] + sorted[sorted.len() / 2]) / 2.0;
    (median, sorted[0], sorted[sorted.len() - 1])
}

fn measure_pair(
    options: &mut Options,
    case: &Case,
    stage: &str,
    mut ours: impl FnMut(),
    mut oracle: impl FnMut(),
) {
    let repeats = [
        calibrate(&mut ours, options.sample_time),
        calibrate(&mut oracle, options.sample_time),
    ];
    let mut samples = [Vec::new(), Vec::new()];
    for sample in 0..options.samples {
        // Alternate engine order to reduce systematic drift from temperature and load.
        for offset in 0..2 {
            let engine = (sample + offset) % 2;
            let elapsed = if engine == 0 {
                time_batch(&mut ours, repeats[0])
            } else {
                time_batch(&mut oracle, repeats[1])
            };
            let ns = elapsed.as_secs_f64() * 1e9 / repeats[engine] as f64;
            samples[engine].push(ns);
            if let Some(csv) = &mut options.csv {
                writeln!(
                    csv,
                    "{},{:?},{},{},{},{},{},{:.3}",
                    case.name,
                    case.profile,
                    stage,
                    ["itasca", "wasmi"][engine],
                    sample + 1,
                    repeats[engine],
                    elapsed.as_nanos(),
                    ns
                )
                .unwrap();
            }
        }
    }
    let a = summary(&samples[0]);
    let b = summary(&samples[1]);
    println!(
        "{:<18} {:<11} {:>10.3} [{:>9.3},{:>9.3}] {:>10.3} [{:>9.3},{:>9.3}] {:>7.2}x",
        case.name,
        stage,
        a.0 / 1000.0,
        a.1 / 1000.0,
        a.2 / 1000.0,
        b.0 / 1000.0,
        b.1 / 1000.0,
        b.2 / 1000.0,
        a.0 / b.0
    );
}

fn main() {
    assert!(!cfg!(debug_assertions), "run with --release");
    let mut options = Options::parse();
    let selected: Vec<_> = cases()
        .into_iter()
        .filter(|case| case.name.contains(&options.filter))
        .collect();
    assert!(!selected.is_empty(), "filter matched no workloads");
    if let Some(csv) = &mut options.csv {
        writeln!(
            csv,
            "workload,profile,stage,engine,sample,iterations,elapsed_ns,ns_per_operation"
        )
        .unwrap();
    }
    println!(
        "Slot itasca vs Wasmi 2.0.0 (eager), {} samples, target {} ms/sample, {}-{}",
        options.samples,
        options.sample_time.as_millis(),
        std::env::consts::ARCH,
        std::env::consts::OS
    );
    println!(
        "Times: median [min,max] microseconds/operation. Ratio = itasca / Wasmi; lower is better."
    );
    println!("Compile includes validation/rewrite/drop and a fresh Wasmi engine; compile_instance also creates the store and instance;");
    println!("execute includes invocation/result handling on reused instances; reuse retains itasca frame/slot storage. WAT encoding excluded.");
    println!("For cross_instance, compile/footprint cover the consumer; compile_instance also compiles its provider. Both engines run without fuel.");
    println!(
        "{:<18} {:<11} {:>32} {:>32} {:>8}",
        "workload", "stage", "itasca us", "Wasmi us", "ratio"
    );
    for case in &selected {
        let buffer = wast::parser::ParseBuffer::new(&case.text).unwrap();
        let bytes = wast::parser::parse::<wast::Wat>(&buffer)
            .unwrap()
            .encode()
            .unwrap();
        let code = compile(&bytes, case.profile).unwrap();
        let engine = oracle_engine(case.profile);
        let oracle_code = wasmi::Module::new(&engine, &bytes).unwrap();
        let provider_bytes = case.provider.as_ref().map(|text| {
            let buffer = wast::parser::ParseBuffer::new(text).unwrap();
            wast::parser::parse::<wast::Wat>(&buffer)
                .unwrap()
                .encode()
                .unwrap()
        });
        let oracle_provider = provider_bytes
            .as_ref()
            .map(|bytes| wasmi::Module::new(&engine, bytes).unwrap());
        let (mut store, function) = our_instance(&bytes, provider_bytes.as_deref(), case.profile);
        let (mut oracle_store, oracle_function) =
            oracle_instance(&engine, &oracle_code, oracle_provider.as_ref());
        for _ in 0..5 {
            let result = our_call(&mut store, function, case.argument, |_| {});
            assert_eq!(result, case.expected, "{} itasca", case.name);
            assert_eq!(
                oracle_call(&mut oracle_store, oracle_function, case.argument),
                case.expected,
                "{} Wasmi",
                case.name
            );
        }
        measure_pair(
            &mut options,
            case,
            "compile",
            || {
                black_box(compile(black_box(&bytes), case.profile).unwrap());
            },
            || {
                // Wasmi stores compiled bodies in its engine's append-only code map.
                // Drop the fresh engine in this iteration so compilation retains no
                // earlier modules and all compiled storage destruction is timed.
                let fresh_engine = oracle_engine(case.profile);
                black_box(wasmi::Module::new(&fresh_engine, black_box(&bytes)).unwrap());
            },
        );
        measure_pair(
            &mut options,
            case,
            "compile_instance",
            || {
                black_box(our_instance(
                    &bytes,
                    provider_bytes.as_deref(),
                    case.profile,
                ));
            },
            || {
                let fresh = oracle_engine(case.profile);
                let module = wasmi::Module::new(&fresh, &bytes).unwrap();
                let provider = provider_bytes
                    .as_ref()
                    .map(|b| wasmi::Module::new(&fresh, b).unwrap());
                black_box(oracle_instance(&fresh, &module, provider.as_ref()));
            },
        );
        measure_pair(
            &mut options,
            case,
            "execute",
            || {
                black_box(our_call(
                    &mut store,
                    function,
                    black_box(case.argument),
                    |_| {},
                ));
            },
            || {
                black_box(oracle_call(
                    &mut oracle_store,
                    oracle_function,
                    black_box(case.argument),
                ));
            },
        );
        let mut reused = Execution::new();
        assert_eq!(
            our_reused_call(&mut store, &mut reused, function, case.argument),
            case.expected
        );
        measure_pair(
            &mut options,
            case,
            "reuse",
            || {
                black_box(our_reused_call(
                    &mut store,
                    &mut reused,
                    function,
                    black_box(case.argument),
                ));
            },
            || {
                black_box(oracle_call(
                    &mut oracle_store,
                    oracle_function,
                    black_box(case.argument),
                ));
            },
        );
        assert_eq!(
            our_reused_call(&mut store, &mut reused, function, case.argument),
            case.expected
        );
        // Check again after all sampling; known-result comparisons stay outside the clocks.
        assert_eq!(
            our_call(&mut store, function, case.argument, |_| {}),
            case.expected
        );
        assert_eq!(
            oracle_call(&mut oracle_store, oracle_function, case.argument),
            case.expected
        );
        let (mut count, mut instructions, mut instruction_bytes, mut branch_bytes, mut slots) =
            (0, 0, 0, 0, 0);
        while let Some(stats) = code.function_stats(count) {
            instructions += stats.instruction_count;
            instruction_bytes += stats.instruction_bytes;
            branch_bytes += stats.branch_table_bytes;
            slots = slots.max(stats.slot_count);
            count += 1;
        }
        println!("  footprint: source={} B, functions={count}, instructions={instructions}, bytecode={instruction_bytes} B, branch_tables={branch_bytes} B, largest_frame_payload={} B, slot_size=8 B",
            bytes.len(), slots * std::mem::size_of::<u64>());
    }
    if let Some(csv) = &mut options.csv {
        csv.flush().unwrap();
    }
}
