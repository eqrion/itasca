//! A small repeatable control-signature benchmark, with encoding outside timing.
//! Run with `cargo run --release --example multi_value_bench`.
use std::hint::black_box;
use std::time::{Duration, Instant};

fn encode(source: &str) -> Vec<u8> {
    let buf = wast::parser::ParseBuffer::new(source).unwrap();
    wast::parser::parse::<wast::Wat>(&buf)
        .unwrap()
        .encode()
        .unwrap()
}

fn measure(bytes: &[u8], profile: itasca::ValidationProfile) -> (usize, Duration) {
    let start = Instant::now();
    let mut runs = 0;
    while start.elapsed() < Duration::from_millis(500) {
        black_box(itasca::validate_module_with_profile(black_box(bytes), profile).unwrap());
        runs += 1;
    }
    (runs, start.elapsed())
}

fn main() {
    for results in [0, 1, 2, 16, 1000] {
        let signature = if results == 0 {
            String::new()
        } else {
            format!("(result {})", "i32 ".repeat(results))
        };
        let blocks = if results <= 16 { 10000 } else { 200 };
        let body = format!(
            "block {signature} unreachable end {}",
            "drop ".repeat(results)
        );
        let bytes = encode(&format!("(module (func {}))", body.repeat(blocks)));
        if results <= 1 {
            let (n, time) = measure(&bytes, itasca::ValidationProfile::Wasm1);
            println!(
                "{results:4} results, Wasm1:     {:.1} ns/block",
                time.as_nanos() as f64 / (n * blocks) as f64
            );
        }
        let (n, time) = measure(&bytes, itasca::ValidationProfile::MultiValue);
        println!(
            "{results:4} results, MultiValue: {:.1} ns/block",
            time.as_nanos() as f64 / (n * blocks) as f64
        );
    }
}
