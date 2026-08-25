//! Tests for the push interface: which hook fires, with what immediates, and
//! what happens when a consumer declines.

use itasca::code::*;
use itasca::error::{OpError, VisitError};
use itasca::module::*;
use itasca::types::*;

fn env_with_memory() -> Env {
    let mut env = Env::new();
    env.mem_types.push(MemType {
        limits: Limits { min: 1, max: None },
    });
    env
}

fn ctx(locals: &[ValueType], results: &[ValueType]) -> Context {
    let mut stack = LocalsStack::new();
    for vt in locals {
        stack.push(*vt);
    }
    Context {
        locals: stack,
        results: results.first().copied(),
    }
}

/// One line per hook, so a test can assert on the whole operator stream.
#[derive(Default)]
struct Recorder {
    ops: Vec<String>,
    /// Stop after this many hooks, reporting `OutOfMemory`. `None` never stops.
    give_up_after: Option<usize>,
}

impl Recorder {
    fn record(&mut self, line: &str) -> VisitResult {
        if let Some(n) = self.give_up_after {
            if self.ops.len() >= n {
                return Err(VisitError::OutOfMemory);
            }
        }
        self.ops.push(line.to_string());
        Ok(())
    }
}

/// Only the hooks these tests assert on. Everything else keeps its default,
/// which is the point of the defaults.
impl OpVisitor for Recorder {
    fn on_unreachable(&mut self, _st: &OpIterState) -> VisitResult {
        self.record("unreachable")
    }
    fn on_nop(&mut self, _st: &OpIterState) -> VisitResult {
        self.record("nop")
    }
    fn on_block(&mut self, _st: &OpIterState, bt: BlockType) -> VisitResult {
        self.record(&format!("block {bt:?}"))
    }
    fn on_loop(&mut self, _st: &OpIterState, bt: BlockType) -> VisitResult {
        self.record(&format!("loop {bt:?}"))
    }
    fn on_if(&mut self, _st: &OpIterState, bt: BlockType) -> VisitResult {
        self.record(&format!("if {bt:?}"))
    }
    fn on_else(&mut self, _st: &OpIterState, bt: BlockType) -> VisitResult {
        self.record(&format!("else {bt:?}"))
    }
    fn on_end(&mut self, _st: &OpIterState, kind: LabelKind, bt: BlockType) -> VisitResult {
        self.record(&format!("end {kind:?} {bt:?}"))
    }
    fn on_br(&mut self, _st: &OpIterState, depth: u32, bt: BlockType) -> VisitResult {
        self.record(&format!("br {depth} {bt:?}"))
    }
    fn on_br_if(&mut self, _st: &OpIterState, depth: u32, bt: BlockType) -> VisitResult {
        self.record(&format!("br_if {depth} {bt:?}"))
    }
    fn on_br_table_label(&mut self, _st: &OpIterState, depth: u32) -> VisitResult {
        self.record(&format!("br_table label {depth}"))
    }
    fn on_br_table(&mut self, _st: &OpIterState, default: u32, common: BlockType) -> VisitResult {
        self.record(&format!("br_table default={default} {common:?}"))
    }
    fn on_return(&mut self, _st: &OpIterState) -> VisitResult {
        self.record("return")
    }
    fn on_call(&mut self, _st: &OpIterState, idx: u32) -> VisitResult {
        self.record(&format!("call {idx}"))
    }
    fn on_call_indirect(&mut self, _st: &OpIterState, idx: u32) -> VisitResult {
        self.record(&format!("call_indirect {idx}"))
    }
    fn on_drop(&mut self, _st: &OpIterState, ty: StackType) -> VisitResult {
        self.record(&format!("drop {ty:?}"))
    }
    fn on_select(&mut self, _st: &OpIterState, ty: StackType) -> VisitResult {
        self.record(&format!("select {ty:?}"))
    }
    fn on_local_get(&mut self, _st: &OpIterState, idx: u32) -> VisitResult {
        self.record(&format!("local.get {idx}"))
    }
    fn on_local_set(&mut self, _st: &OpIterState, idx: u32) -> VisitResult {
        self.record(&format!("local.set {idx}"))
    }
    fn on_local_tee(&mut self, _st: &OpIterState, idx: u32) -> VisitResult {
        self.record(&format!("local.tee {idx}"))
    }
    fn on_global_get(&mut self, _st: &OpIterState, idx: u32) -> VisitResult {
        self.record(&format!("global.get {idx}"))
    }
    fn on_memory_size(&mut self, _st: &OpIterState) -> VisitResult {
        self.record("memory.size")
    }
    fn on_memory_grow(&mut self, _st: &OpIterState) -> VisitResult {
        self.record("memory.grow")
    }
    fn on_i32_const(&mut self, st: &OpIterState, v: i32) -> VisitResult {
        self.record(&format!("i32.const {v} @{}", st.pos))
    }
    fn on_i64_const(&mut self, _st: &OpIterState, v: i64) -> VisitResult {
        self.record(&format!("i64.const {v}"))
    }
    fn on_f32_const(&mut self, _st: &OpIterState, bits: u32) -> VisitResult {
        self.record(&format!("f32.const {bits:#x}"))
    }
    fn on_f64_const(&mut self, _st: &OpIterState, bits: u64) -> VisitResult {
        self.record(&format!("f64.const {bits:#x}"))
    }
    fn on_i32_load(&mut self, _st: &OpIterState, m: MemArg) -> VisitResult {
        self.record(&format!("i32.load align={} offset={}", m.align, m.offset))
    }
    fn on_i32_store8(&mut self, _st: &OpIterState, m: MemArg) -> VisitResult {
        self.record(&format!("i32.store8 align={} offset={}", m.align, m.offset))
    }
    fn on_i32_add(&mut self, _st: &OpIterState) -> VisitResult {
        self.record("i32.add")
    }
    fn on_i32_sub(&mut self, _st: &OpIterState) -> VisitResult {
        self.record("i32.sub")
    }
    fn on_i32_eqz(&mut self, _st: &OpIterState) -> VisitResult {
        self.record("i32.eqz")
    }
    fn on_i64_extend_i32_s(&mut self, _st: &OpIterState) -> VisitResult {
        self.record("i64.extend_i32_s")
    }
    fn on_f64_max(&mut self, _st: &OpIterState) -> VisitResult {
        self.record("f64.max")
    }
    fn on_f32_reinterpret_i32(&mut self, _st: &OpIterState) -> VisitResult {
        self.record("f32.reinterpret_i32")
    }
}

fn record(body: &[u8], locals: &[ValueType], results: &[ValueType]) -> Vec<String> {
    let mut r = Recorder::default();
    let verdict = validate_body_with(body, &env_with_memory(), &ctx(locals, results), &mut r);
    assert_eq!(verdict, Ok(()), "body was rejected: {:?}", verdict);
    r.ops
}

// ---- The immediates reach the hooks ----

#[test]
fn constants_carry_their_immediates_and_the_cursor() {
    // The cursor a hook sees is the position just past the operator.
    assert_eq!(
        record(&[OP_I32_CONST, 0x7f, OP_DROP, OP_END], &[], &[]),
        ["i32.const -1 @2", "drop Val(I32)", "end Body Empty"]
    );
    assert_eq!(
        record(&[OP_I64_CONST, 0xc0, 0xbb, 0x78, OP_DROP, OP_END], &[], &[]),
        ["i64.const -123456", "drop Val(I64)", "end Body Empty"]
    );
    assert_eq!(
        record(
            &[OP_F32_CONST, 0x00, 0x00, 0x80, 0x3f, OP_DROP, OP_END],
            &[],
            &[]
        ),
        ["f32.const 0x3f800000", "drop Val(F32)", "end Body Empty"]
    );
    assert_eq!(
        record(
            &[OP_F64_CONST, 0, 0, 0, 0, 0, 0, 0xf0, 0x3f, OP_DROP, OP_END],
            &[],
            &[]
        ),
        [
            "f64.const 0x3ff0000000000000",
            "drop Val(F64)",
            "end Body Empty"
        ]
    );
}

#[test]
fn variables_and_memory_carry_their_immediates() {
    assert_eq!(
        record(
            &[
                OP_LOCAL_GET,
                1,
                OP_LOCAL_SET,
                1,
                OP_LOCAL_GET,
                0,
                OP_LOCAL_TEE,
                0,
                OP_DROP,
                OP_END
            ],
            &[ValueType::I32, ValueType::I32],
            &[]
        ),
        [
            "local.get 1",
            "local.set 1",
            "local.get 0",
            "local.tee 0",
            "drop Val(I32)",
            "end Body Empty"
        ]
    );
    // align and offset arrive as the encoding gave them.
    assert_eq!(
        record(
            &[OP_I32_CONST, 0, OP_I32_LOAD, 2, 8, OP_DROP, OP_END],
            &[],
            &[]
        ),
        [
            "i32.const 0 @2",
            "i32.load align=2 offset=8",
            "drop Val(I32)",
            "end Body Empty"
        ]
    );
    assert_eq!(
        record(
            &[
                OP_I32_CONST,
                0,
                OP_I32_CONST,
                0,
                OP_I32_STORE8,
                0,
                0x10,
                OP_END
            ],
            &[],
            &[]
        ),
        [
            "i32.const 0 @2",
            "i32.const 0 @4",
            "i32.store8 align=0 offset=16",
            "end Body Empty"
        ]
    );
    assert_eq!(
        record(
            &[OP_MEMORY_SIZE, 0, OP_MEMORY_GROW, 0, OP_DROP, OP_END],
            &[],
            &[]
        ),
        [
            "memory.size",
            "memory.grow",
            "drop Val(I32)",
            "end Body Empty"
        ]
    );
}

#[test]
fn control_operators_carry_their_block_types_and_depths() {
    assert_eq!(
        record(
            &[OP_BLOCK, 0x7f, OP_I32_CONST, 1, OP_END, OP_DROP, OP_END],
            &[],
            &[]
        ),
        [
            "block Value(I32)",
            "i32.const 1 @4",
            "end Block Value(I32)",
            "drop Val(I32)",
            "end Body Empty"
        ]
    );
    // a loop's branch target is its parameters, which 1.0 has none of
    assert_eq!(
        record(&[OP_LOOP, 0x40, OP_BR, 0, OP_END, OP_END], &[], &[]),
        [
            "loop Empty",
            "br 0 Empty",
            "end Loop Empty",
            "end Body Empty"
        ]
    );
    // `if` with no `else`: the frame closes as Then, so a consumer knows the
    // empty else was elided
    assert_eq!(
        record(&[OP_I32_CONST, 0, OP_IF, 0x40, OP_END, OP_END], &[], &[]),
        [
            "i32.const 0 @2",
            "if Empty",
            "end Then Empty",
            "end Body Empty"
        ]
    );
    assert_eq!(
        record(
            &[OP_I32_CONST, 0, OP_IF, 0x40, OP_ELSE, OP_END, OP_END],
            &[],
            &[]
        ),
        [
            "i32.const 0 @2",
            "if Empty",
            "else Empty",
            "end Else Empty",
            "end Body Empty"
        ]
    );
    assert_eq!(
        record(
            &[
                OP_BLOCK,
                0x40,
                OP_I32_CONST,
                0,
                OP_BR_IF,
                0,
                OP_I32_CONST,
                0,
                OP_BR_TABLE,
                1,
                0,
                0,
                OP_END,
                OP_END
            ],
            &[],
            &[]
        ),
        [
            "block Empty",
            "i32.const 0 @4",
            "br_if 0 Empty",
            "i32.const 0 @8",
            "br_table label 0",
            "br_table default=0 Empty",
            "end Block Empty",
            "end Body Empty"
        ]
    );
    assert_eq!(
        record(&[OP_RETURN, OP_END], &[], &[]),
        ["return", "end Body Empty"]
    );
}

#[test]
fn select_and_drop_report_the_operand_type() {
    assert_eq!(
        record(
            &[
                OP_I64_CONST,
                1,
                OP_I64_CONST,
                2,
                OP_I32_CONST,
                0,
                OP_SELECT,
                OP_DROP,
                OP_END
            ],
            &[],
            &[]
        ),
        [
            "i64.const 1",
            "i64.const 2",
            "i32.const 0 @6",
            "select Val(I64)",
            "drop Val(I64)",
            "end Body Empty"
        ]
    );
}

#[test]
fn unreachable_code_reports_bottom() {
    // After `unreachable` the frame is polymorphic, so the pop yields `Bot`.
    assert_eq!(
        record(&[OP_UNREACHABLE, OP_DROP, OP_END], &[], &[]),
        ["unreachable", "drop Bot", "end Body Empty"]
    );
}

// ---- The numeric fan-out ----

/// A sample; `OpIter_Table.visit_numeric_names_convert` and its three siblings
/// prove the same thing for every row of both tables, against the instruction
/// table `Spec_Binary.op_spec` transcribes.
#[test]
fn each_numeric_opcode_reaches_its_own_hook() {
    assert_eq!(
        record(
            &[
                OP_I32_CONST,
                1,
                OP_I32_CONST,
                2,
                OP_I32_ADD,
                OP_DROP,
                OP_END
            ],
            &[],
            &[]
        )[2],
        "i32.add"
    );
    assert_eq!(
        record(
            &[
                OP_I32_CONST,
                1,
                OP_I32_CONST,
                2,
                OP_I32_SUB,
                OP_DROP,
                OP_END
            ],
            &[],
            &[]
        )[2],
        "i32.sub"
    );
    assert_eq!(
        record(&[OP_I32_CONST, 1, OP_I32_EQZ, OP_DROP, OP_END], &[], &[])[1],
        "i32.eqz"
    );
    assert_eq!(
        record(
            &[OP_I32_CONST, 1, OP_I64_EXTEND_I32_S, OP_DROP, OP_END],
            &[],
            &[]
        )[1],
        "i64.extend_i32_s"
    );
    assert_eq!(
        record(
            &[
                OP_F64_CONST,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                OP_F64_CONST,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                OP_F64_MAX,
                OP_DROP,
                OP_END
            ],
            &[],
            &[]
        )[2],
        "f64.max"
    );
    assert_eq!(
        record(
            &[OP_I32_CONST, 1, OP_F32_REINTERPRET_I32, OP_DROP, OP_END],
            &[],
            &[]
        )[1],
        "f32.reinterpret_i32"
    );
}

#[test]
fn a_numeric_opcode_with_no_override_is_still_validated() {
    // `i32.mul` keeps its default hook, so nothing is recorded for it, and the
    // body is still accepted.
    assert_eq!(
        record(
            &[
                OP_I32_CONST,
                1,
                OP_I32_CONST,
                2,
                OP_I32_MUL,
                OP_DROP,
                OP_END
            ],
            &[],
            &[]
        ),
        [
            "i32.const 1 @2",
            "i32.const 2 @4",
            "drop Val(I32)",
            "end Body Empty"
        ]
    );
}

// ---- Declining ----

#[test]
fn a_consumer_may_decline_a_valid_body() {
    let body = [
        OP_I32_CONST,
        1,
        OP_I32_CONST,
        2,
        OP_I32_ADD,
        OP_DROP,
        OP_END,
    ];
    let env = env_with_memory();
    let c = ctx(&[], &[]);

    // The body is valid.
    assert_eq!(validate_body(&body, &env, &c), Ok(()));

    let mut r = Recorder {
        give_up_after: Some(2),
        ..Default::default()
    };
    assert_eq!(
        validate_body_with(&body, &env, &c, &mut r),
        Err(OpError::Visitor(VisitError::OutOfMemory))
    );
    // Declining stops the loop, so nothing past the refusal was pushed.
    assert_eq!(r.ops, ["i32.const 1 @2", "i32.const 2 @4"]);
}

#[test]
fn an_invalid_body_is_rejected_for_its_own_reason() {
    let mut r = Recorder::default();
    assert_eq!(
        validate_body_with(
            &[OP_I32_ADD, OP_END],
            &env_with_memory(),
            &ctx(&[], &[]),
            &mut r
        ),
        Err(OpError::EmptyStack)
    );
}

// ---- The no-op instance ----

#[test]
fn the_nop_visitor_agrees_with_validate_body() {
    let env = env_with_memory();
    let c = ctx(&[ValueType::I32], &[]);
    let bodies: &[&[u8]] = &[
        &[OP_END],
        &[OP_NOP, OP_END],
        &[OP_I32_CONST, 1, OP_DROP, OP_END],
        &[OP_LOCAL_GET, 0, OP_DROP, OP_END],
        &[OP_BLOCK, 0x40, OP_END, OP_END],
        // invalid: a pop with nothing on the stack
        &[OP_DROP, OP_END],
        // invalid: an opcode Wasm 1.0 has no row for
        &[0xfe, OP_END],
        // invalid: nothing after the body's end
        &[OP_END, OP_NOP],
        // invalid: truncated
        &[OP_I32_CONST],
    ];
    for body in bodies {
        let mut nop = EmptyOpVisitor;
        assert_eq!(
            validate_body_with(body, &env, &c, &mut nop),
            validate_body(body, &env, &c),
            "disagreed on {body:?}"
        );
    }
}

// ---- The function around the operators ----

/// Records the locals and results a code entry declared, so a test can check
/// the consumer is told what to size a frame from.
#[derive(Default)]
struct FrameRecorder {
    frames: Vec<String>,
    /// The byte range the frame hook reported, so a test can check it against
    /// the module rather than only against a string.
    body: Option<(usize, usize)>,
}

impl OpVisitor for FrameRecorder {
    fn on_function_start(
        &mut self,
        ctx: &Context,
        type_idx: u32,
        body_begin: usize,
        body_end: usize,
    ) -> VisitResult {
        let mut locals = Vec::new();
        for i in 0..ctx.locals.len() {
            locals.push(ctx.locals.get(i));
        }
        self.frames.push(format!(
            "type={type_idx} locals={:?} results={:?} bytes={body_begin}..{body_end}",
            locals, ctx.results
        ));
        self.body = Some((body_begin, body_end));
        Ok(())
    }
}

#[test]
fn a_code_entry_hands_over_its_frame() {
    // (module (func (param i32) (local i64 i64) (result i32) local.get 0))
    let wasm = wat_module();
    let (env, pos) = itasca::module::validate_env(&wasm).expect("env");
    // `pos` is the code section's id byte; one entry, so id + size + count = 3
    let mut r = FrameRecorder::default();
    let end_pos = itasca::module::validate_code_entry_with(&wasm, pos + 3, &env, 0, &mut r);
    assert!(end_pos.is_ok(), "entry rejected: {:?}", end_pos);
    // params come first, then the declared locals, in order
    assert_eq!(
        r.frames,
        ["type=0 locals=[I32, I64, I64] results=Some(I32) bytes=27..30"]
    );
    // And the range really brackets the operators: past the locals declaration
    // at one end, at the entry's end at the other.
    let (begin, end) = r.body.expect("the frame hook did not fire");
    assert_eq!(&wasm[begin..end], &[OP_LOCAL_GET, 0x00, OP_END]);
    assert_eq!(end, *end_pos.as_ref().unwrap());
}

/// The smallest module with one such function, assembled by hand: a code
/// section is the only place locals are declared.
fn wat_module() -> Vec<u8> {
    let mut m = vec![0x00, b'a', b's', b'm', 0x01, 0x00, 0x00, 0x00];
    // type section: (i32) -> (i32)
    m.extend_from_slice(&[0x01, 0x06, 0x01, 0x60, 0x01, 0x7f, 0x01, 0x7f]);
    // function section: one function of type 0
    m.extend_from_slice(&[0x03, 0x02, 0x01, 0x00]);
    // code section: one entry, two i64 locals, body `local.get 0`
    let body: &[u8] = &[
        0x01, // one local run
        0x02,
        0x7e, // two i64
        OP_LOCAL_GET,
        0x00,
        OP_END,
    ];
    m.push(0x0a);
    m.push((body.len() + 2) as u8);
    m.push(0x01);
    m.push(body.len() as u8);
    m.extend_from_slice(body);
    m
}

#[test]
fn a_br_table_hands_over_every_label() {
    // `br_table 1 0 2` inside two blocks: three entries, then the default.
    assert_eq!(
        record(
            &[
                OP_BLOCK,
                0x40,
                OP_BLOCK,
                0x40,
                OP_I32_CONST,
                0,
                OP_BR_TABLE,
                3,
                1,
                0,
                1,
                2,
                OP_END,
                OP_END,
                OP_END
            ],
            &[],
            &[]
        ),
        [
            "block Empty",
            "block Empty",
            "i32.const 0 @6",
            "br_table label 1",
            "br_table label 0",
            "br_table label 1",
            "br_table default=2 Empty",
            "end Block Empty",
            "end Block Empty",
            "end Body Empty"
        ]
    );
}
