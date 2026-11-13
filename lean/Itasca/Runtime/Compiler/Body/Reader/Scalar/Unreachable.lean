import Itasca.Runtime.Compiler.Local.Lowering.Literal.LiteralSources
import Itasca.Runtime.Compiler.Local.Source.SourceLengthsTactic
import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericLowering
import Itasca.Runtime.Compiler.Local.Lowering.Local.LoweringLocal
import Itasca.Runtime.Compiler.Local.Source.SourceCursorTactic
import Itasca.Runtime.Compiler.Body.Source.TypedLowering
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Body.Reader.Replay.BulkAndSaturatingAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Replay.Post
import Itasca.Runtime.Compiler.Local.Relations.Prefix.SuspendedPrefix
import Itasca.Runtime.Compiler.Body.Reader.Stacks.Values
import Itasca.Wasm2.Scalar.NumericReader
import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericOpcode
import Itasca.Runtime.Compiler.Local.Relations.Emission.Rel
import Itasca.Wasm2.NumericExt.Sound
import Itasca.Visitor.EventTables
import Itasca.Runtime.Compiler.Local.Lowering.Float.FloatLowering
import Itasca.Runtime.Compiler.Local.Lowering.Float.FloatEncoding
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Wasm2.Scalar.StackReader
import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty
import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericOperands
import Itasca.Runtime.Compiler.Local.Relations.Stacks.KnownStackTransfer
import Itasca.Runtime.Compiler.Body.Reader.Local.Wasm2Local
import Itasca.Runtime.Compiler.Local.Relations.Operations.CoreBasicEmissions
import Itasca.Runtime.Compiler.Local.Relations.Emission.CoreLoweringEffects
import Itasca.Wasm2.Scalar.BasicReader
import Itasca.Runtime.Compiler.Local.Relations.Control.KnownControlStack

/-!
Sections, each formerly its own module: Emissions, SignExtension, Saturating, SaturatingEmissions, Empty, IntegerFacts, NumericEmissions, SelectTypes, SelectEmissions, SignEmissions, Unreachable.
-/

/-! ## Emissions -/

section

/-!
An actual successful constant reader and compiler callback extends the retained code prefix and the supplied source zipper together.

Main declarations: `reader_emit_const32_wasm2` and `reader_emit_const64_wasm2`. A direct consumer is `Compiler.Body.Reader.Checking.ScalarInstructionPrefixWasm2`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- An actual successful constant reader and compiler callback extends the
retained code prefix and the supplied source zipper together. -/
theorem reader_emit_const32_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (types : List wasm_types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translate.valueType))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_I32_CONST)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_I32_CONST before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.core.pos ∧
    (∃ value,
      Wasm2.ReaderPost p out.core (Spec.i32Const value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [.Val .I32]) ∧
      ∃ emitted, TypedLowered before after out.core.vals.val emitted (types.map Translate.valueType ++ [.I32]) ∧
        LinearEmission (compilerLocals before) (types.map Translate.valueType) (Spec.i32Const value) [emitted]
          (types.map Translate.valueType ++ [.I32])) := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals, p.ft.results⟩ index code.OP_I32_CONST before after (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨value, callback, _, vals, post⟩ := reader_i32_const_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity byte run
  have postConcrete : out.core.vals.val = (types ++ [Itasca.wasm_types.ValueType.I32]).map code.StackType.Val := by
    simp [vals, concrete]
  have lowered := callback_const32 ops law before out.core (types ++ [Itasca.wasm_types.ValueType.I32])
    (types.map Translate.valueType) value layout reachable postConcrete codeFits sourceFits coordinateFits
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_const ops before out.core value = _ at callback
  have ordinary := compiler_i32_const_ordinary_result ops law before after out.core value (.Ok ()) callback
  have sources := compiler_i32_const_sources ops law before after out.core value callback
  have cursor := compiler_i32_const_cursor ops law before after out.core value callback
  refine ⟨ordinary, sources, cursor, ?_⟩
  rw [callback, WP.spec_ok] at lowered
  have lower := lowered rfl
  simp only [List.map_append, List.map_cons, List.map_nil, Translate.valueType] at lower
  have instruction : Spec.i32Const value =
      .CONST .I32 (.mk_num__0 .I32 (.mk_uN (IScalar.hcast .U32 value).val)) := by rfl
  refine ⟨value, post, _, ⟨lower, SourceStack.of_map (types ++ [.I32]) postConcrete (by simp [Translate.valueType])⟩, ?_⟩
  rw [instruction]
  apply LinearEmission.const32
  exact layout.height

/-- An actual successful constant reader and compiler callback extends the
retained code prefix and the supplied source zipper together. -/
theorem reader_emit_const64_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (types : List wasm_types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translate.valueType))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_I64_CONST)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_I64_CONST before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.core.pos ∧
    (∃ value,
      Wasm2.ReaderPost p out.core (ScalarConst.i64 value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [.Val .I64]) ∧
      ∃ emitted, TypedLowered before after out.core.vals.val emitted (types.map Translate.valueType ++ [.I64]) ∧
        LinearEmission (compilerLocals before) (types.map Translate.valueType) (ScalarConst.i64 value) [emitted]
          (types.map Translate.valueType ++ [.I64])) := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals, p.ft.results⟩ index code.OP_I64_CONST before after (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨value, callback, _, vals, post⟩ := reader_i64_const_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity byte run
  have postConcrete : out.core.vals.val = (types ++ [Itasca.wasm_types.ValueType.I64]).map code.StackType.Val := by
    simp [vals, concrete]
  have lowered := callback_const64 ops law before out.core (types ++ [Itasca.wasm_types.ValueType.I64])
    (types.map Translate.valueType) value layout reachable postConcrete codeFits sourceFits coordinateFits
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_const ops before out.core value = _ at callback
  have ordinary := compiler_i64_const_ordinary_result ops law before after out.core value (.Ok ()) callback
  have sources := compiler_i64_const_sources ops law before after out.core value callback
  have cursor := compiler_i64_const_cursor ops law before after out.core value callback
  refine ⟨ordinary, sources, cursor, ?_⟩
  rw [callback, WP.spec_ok] at lowered
  have lower := lowered rfl
  simp only [List.map_append, List.map_cons, List.map_nil, Translate.valueType] at lower
  have instruction : ScalarConst.i64 value =
      .CONST .I64 (.mk_num__0 .I64 (.mk_uN (IScalar.hcast .U64 value).val)) := by rfl
  refine ⟨value, post, _, ⟨lower, SourceStack.of_map (types ++ [.I64]) postConcrete (by simp [Translate.valueType])⟩, ?_⟩
  rw [instruction]
  apply LinearEmission.const64
  exact layout.height

end Itasca.Runtime.Compiler

end

/-! ## SignExtension -/

section

/-!
Exact sign-extension reading advances the supplied source zipper and retains both the physical conversion and actual visitor callback.

Main declarations: `reader_sign_wasm2` and `reader_integer_sign_wasm2`. A direct consumer is `Compiler.Body.Reader.Checking.OperationInstructionPrefix`.
-/

set_option maxHeartbeats 1000000
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Exact sign-extension reading advances the supplied source zipper and
retains both the physical conversion and actual visitor callback. -/
theorem reader_sign_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState) (ctx : code.Context) (opcode : U8)
    (operation : Numeric.Operation)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (meaning : Wasm2.NumericExtensions.signMeaning opcode = some operation)
    (accepted : code.step_extended visitor st.core data env ctx opcode before =
      .ok (.Ok (), out, after)) :
    code.visit_sign_extension visitor before out opcode = .ok (.Ok (), after) ∧
      Numeric.read operation st.core = .ok (.Ok (), out) ∧
      code.read_conversion st.core operation.input operation.output = .ok (.Ok (), out) ∧
      out.ctrls = st.core.ctrls ∧ out.pos = st.core.pos ∧
      ∃ values, StackSemantics.NumericEffect p.current.ctrl.polymorphic_base p.current.vals
          operation.inputs operation.output values ∧
        Wasm2.ReaderPost p out operation.instruction p.current.ctrl.polymorphic_base values := by
  rw [code.step_extended.sign visitor st.core data env ctx opcode operation before meaning] at accepted
  obtain ⟨unit, converted, callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
  cases unit
  have unary := (Wasm2.NumericExtensions.sign_properties meaning).1
  have read : Numeric.read operation st.core = .ok (.Ok (), out) := by
    simpa only [Numeric.read, unary, Bool.false_eq_true, ↓reduceIte] using converted
  have encoded : Wasm2.At data p.start (.plain operation.instruction) st.core.pos :=
    .of_immediate p.inbounds byte p.pos (.signExtension opcode operation meaning)
      (Wasm1.BytesAt.nil data st.core.pos (by have := p.pos; have := p.inbounds; omega))
  have effect := p.numeric_reader operation st.core.pos capacity encoded (Wasm2.NumericExtensions.sign_declared meaning _)
  dsimp only at effect
  rw [read, WP.spec_ok] at effect
  obtain ⟨controls, position, rest⟩ := effect
  obtain ⟨values, numeric, post⟩ := rest () rfl
  exact ⟨callback, read, converted, controls, position, values, numeric, post⟩

/-- The five Wasm2 sign extensions match their canonical operation and visitor
hook, and invoke the ordinary integer lowering entry with their exact opcode. -/
theorem integer_sign_reader_facts {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState)
    (op : SourceMachine.Numeric.Instruction) (extension : 192 ≤ (integerOpcode op).val) :
    ∃ (operation : Numeric.Operation) (hook : ExtendedNumericHook),
      Wasm2.NumericExtensions.signMeaning (UScalar.cast .U8 (integerOpcode op)) = some operation ∧
      operation.instruction = op.source ∧
      operation.inputs.map Translate.valueType = List.replicate op.arity (integerType op.input) ∧
      Translate.valueType operation.output = integerType op.output ∧
      hook.encoding = (UScalar.cast .U8 (integerOpcode op), none) ∧
      invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler (.op state (.extendedNumeric hook)) =
        runtime.compiler.lower.FunctionCompiler.op ops compiler state (integerOpcode op) 0#u32 0#u32 0#u128 ∧
      (UScalar.cast .U8 (integerOpcode op)).val ∉ Wasm2.controlOpcodes ∧
      (UScalar.cast .U8 (integerOpcode op)).val ∉ [28, 37, 38, 208, 209, 210, 252, 253] := by
  cases op with
  | binary ty operator =>
    cases ty <;> cases operator <;> (try (rename_i sign; cases sign)) <;>
      norm_num [integerOpcode] at extension
  | compare ty operator =>
    cases ty <;> cases operator <;> (try (rename_i sign; cases sign)) <;>
      norm_num [integerOpcode] at extension
  | unary ty operator =>
    cases ty with
    | I32 =>
      cases operator with
      | clz | ctz | popcnt => norm_num [integerOpcode] at extension
      | extend8 => exact ⟨_, .i32_extend8_s, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide⟩
      | extend16 => exact ⟨_, .i32_extend16_s, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide⟩
    | I64 =>
      cases operator with
      | clz | ctz | popcnt => norm_num [integerOpcode] at extension
      | extend8 => exact ⟨_, .i64_extend8_s, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide⟩
      | extend16 => exact ⟨_, .i64_extend16_s, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide⟩
      | extend32 => exact ⟨_, .i64_extend32_s, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide⟩
  | eqz ty => cases ty <;> norm_num [integerOpcode] at extension
  | conversion operator => cases operator <;> norm_num [integerOpcode] at extension

/-- Successful profile dispatch for any of the five sign extensions supplies
all reader capacity, hook identity and exact source-position facts internally. -/
theorem reader_integer_sign_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (op : SourceMachine.Numeric.Instruction)
    (extension : 192 ≤ (integerOpcode op).val)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (), out, after)) :
    ∃ operation : Numeric.Operation,
      operation.instruction = op.source ∧
      operation.inputs.map Translate.valueType = List.replicate op.arity (integerType op.input) ∧
      Translate.valueType operation.output = integerType op.output ∧
      runtime.compiler.lower.FunctionCompiler.op ops before out.core (integerOpcode op) 0#u32 0#u32 0#u128 =
        .ok (.Ok (), after) ∧
      Numeric.read operation st.core = .ok (.Ok (), out.core) ∧
      code.read_conversion st.core operation.input operation.output = .ok (.Ok (), out.core) ∧
      out.core.ctrls = st.core.ctrls ∧ out.core.pos = st.core.pos ∧
      ∃ values, StackSemantics.NumericEffect p.current.ctrl.polymorphic_base p.current.vals
          operation.inputs operation.output values ∧
        Wasm2.ReaderPost p out.core op.source p.current.ctrl.polymorphic_base values := by
  obtain ⟨operation, hook, meaning, instruction, inputs, output, encoding, hookEq, ordinary, base⟩ :=
    integer_sign_reader_facts ops before out.core op extension
  obtain ⟨capacity, run⟩ := profile_scalar_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index _ before after ordinary accepted
  rw [code.step_wasm2.base _ _ _ _ _ _ _ base] at run
  obtain ⟨callback, read, converted, controls, position, values, numeric, post⟩ :=
    reader_sign_wasm2 p (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      before after out.core ctx _ operation capacity byte meaning run
  have dispatch := ExtendedNumericHook.dispatch
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before out.core hook
  rw [encoding] at dispatch
  dsimp only at dispatch
  rw [dispatch, hookEq] at callback
  exact ⟨operation, instruction, inputs, output, callback, read, converted, controls, position,
    values, numeric, instruction ▸ post⟩

end Itasca.Runtime.Compiler

end

/-! ## Saturating -/

section

/-!
Reader inversion for saturating floating-point conversions.

Main declarations: `reader_saturating_wasm2` and `reader_float_saturating_wasm2`. A direct consumer is `Compiler.Body.Reader.Acceptance.SourceBoundNumericExtensionAcceptance`.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
theorem reader_saturating_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState) (ctx : code.Context) (subopcode : U32) (next : Usize)
    (operation : Numeric.Operation)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 0xfc#u8)
    (decoded : Leb128.Decoded data st.core.pos subopcode next)
    (meaning : Wasm2.NumericExtensions.saturatingMeaning subopcode = some operation)
    (accepted : code.step_extended visitor st.core data env ctx 0xfc#u8 before =
      .ok (.Ok (), out, after)) :
    code.visit_saturating visitor before out subopcode = .ok (.Ok (), after) ∧
      Numeric.read operation {st.core with pos := next} = .ok (.Ok (), out) ∧
      code.read_conversion {st.core with pos := next} operation.input operation.output = .ok (.Ok (), out) ∧
      out.ctrls = st.core.ctrls ∧ out.pos = next ∧
      ∃ values, StackSemantics.NumericEffect p.current.ctrl.polymorphic_base p.current.vals
          operation.inputs operation.output values ∧
        Wasm2.ReaderPost p out operation.instruction p.current.ctrl.polymorphic_base values := by
  have readLeb := reader.read_u32_leb.complete data st.core.pos subopcode next decoded
  rw [code.step_extended.prefixed] at accepted
  simp only [Wasm2.prefixedStep, readLeb, bind_ok, meaning] at accepted
  obtain ⟨unit, converted, callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
  cases unit
  have unary := Wasm2.NumericExtensions.saturating_unary meaning
  have read : Numeric.read operation {st.core with pos := next} = .ok (.Ok (), out) := by
    simpa only [Numeric.read, unary, Bool.false_eq_true, ↓reduceIte] using converted
  have encoded : Wasm2.At data p.start (.plain operation.instruction) next := by
    obtain ⟨bytes, first, last, slice, leb⟩ := decoded
    exact Wasm2.At.of_immediate p.inbounds byte p.pos (.saturating subopcode operation meaning leb)
      (show Wasm1.BytesAt data st.core.pos bytes next from ⟨first, last, slice⟩)
  have effect := p.numeric_reader operation next capacity encoded (Wasm2.NumericExtensions.saturating_declared meaning _)
  dsimp only at effect
  rw [read, WP.spec_ok] at effect
  obtain ⟨controls, position, rest⟩ := effect
  obtain ⟨values, numeric, post⟩ := rest () rfl
  exact ⟨callback, read, converted, controls, position, values, numeric, post⟩

theorem float_saturating_reader_facts {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState)
    (op : SourceMachine.Float.Instruction) (extension : 256 ≤ (floatOpcode op).val) :
    ∃ (subopcode : U32) (operation : Numeric.Operation) (hook : ExtendedNumericHook),
      subopcode.val = (floatOpcode op).val - 256 ∧ subopcode.val < 8 ∧
      Wasm2.NumericExtensions.saturatingMeaning subopcode = some operation ∧
      operation.instruction = op.source ∧
      operation.inputs.map Translate.valueType = List.replicate op.arity (valtype_numtype op.input) ∧
      Translate.valueType operation.output = valtype_numtype op.output ∧
      hook.encoding = (0xfc#u8, some subopcode) ∧
      invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler (.op state (.extendedNumeric hook)) =
        runtime.compiler.lower.FunctionCompiler.op ops compiler state (floatOpcode op) 0#u32 0#u32 0#u128 := by
  change 256 ≤ op.opcode at extension
  cases op with
  | unary ty operator => cases ty <;> cases operator <;> norm_num [SourceMachine.Float.Instruction.opcode,SourceMachine.Float.signIndex, SourceMachine.Float.unaryIndex, SourceMachine.Float.binaryIndex, SourceMachine.Float.compareIndex] at extension
  | binary ty operator => cases ty <;> cases operator <;> norm_num [SourceMachine.Float.Instruction.opcode,SourceMachine.Float.signIndex, SourceMachine.Float.unaryIndex, SourceMachine.Float.binaryIndex, SourceMachine.Float.compareIndex] at extension
  | compare ty operator => cases ty <;> cases operator <;> norm_num [SourceMachine.Float.Instruction.opcode,SourceMachine.Float.signIndex, SourceMachine.Float.unaryIndex, SourceMachine.Float.binaryIndex, SourceMachine.Float.compareIndex] at extension
  | convert source target sign => cases source <;> cases target <;> cases sign <;> norm_num [SourceMachine.Float.Instruction.opcode,SourceMachine.Float.signIndex, SourceMachine.Float.unaryIndex, SourceMachine.Float.binaryIndex, SourceMachine.Float.compareIndex] at extension
  | reinterpretFloat source => cases source <;> norm_num [SourceMachine.Float.Instruction.opcode,SourceMachine.Float.signIndex, SourceMachine.Float.unaryIndex, SourceMachine.Float.binaryIndex, SourceMachine.Float.compareIndex] at extension
  | reinterpretInt source => cases source <;> norm_num [SourceMachine.Float.Instruction.opcode,SourceMachine.Float.signIndex, SourceMachine.Float.unaryIndex, SourceMachine.Float.binaryIndex, SourceMachine.Float.compareIndex] at extension
  | promote | demote => skip <;> norm_num [SourceMachine.Float.Instruction.opcode,SourceMachine.Float.signIndex, SourceMachine.Float.unaryIndex, SourceMachine.Float.binaryIndex, SourceMachine.Float.compareIndex] at extension
  | truncate source target sign saturating =>
    cases saturating with
    | false => cases source <;> cases target <;> cases sign <;> norm_num [SourceMachine.Float.Instruction.opcode,SourceMachine.Float.signIndex, SourceMachine.Float.unaryIndex, SourceMachine.Float.binaryIndex, SourceMachine.Float.compareIndex] at extension
    | true =>
      cases source with
      | F32 =>
        cases target with
        | I32 =>
          cases sign with
          | S => exact ⟨0#u32, _, .i32_trunc_sat_f32_s, rfl, by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩
          | U => exact ⟨1#u32, _, .i32_trunc_sat_f32_u, rfl, by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩
        | I64 =>
          cases sign with
          | S => exact ⟨4#u32, _, .i64_trunc_sat_f32_s, rfl, by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩
          | U => exact ⟨5#u32, _, .i64_trunc_sat_f32_u, rfl, by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩
      | F64 =>
        cases target with
        | I32 =>
          cases sign with
          | S => exact ⟨2#u32, _, .i32_trunc_sat_f64_s, rfl, by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩
          | U => exact ⟨3#u32, _, .i32_trunc_sat_f64_u, rfl, by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩
        | I64 =>
          cases sign with
          | S => exact ⟨6#u32, _, .i64_trunc_sat_f64_s, rfl, by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩
          | U => exact ⟨7#u32, _, .i64_trunc_sat_f64_u, rfl, by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Saturating float lowering consumes the canonical complete LEB immediate
and advances the same pending source zipper as the actual profile reader. -/
theorem reader_float_saturating_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (op : SourceMachine.Float.Instruction)
    (extension : 256 ≤ (floatOpcode op).val)
    (subopcode : U32) (next : Usize)
    (subopcodeEq : subopcode.val = (floatOpcode op).val - 256)
    (decoded : Leb128.Decoded data st.core.pos subopcode next)
    (byte : data.val[p.start.val]'p.inbounds = 0xfc#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 0xfc#u8 before = .ok (.Ok (),out,after)) :
    ∃ operation : Numeric.Operation,
      operation.instruction = op.source ∧
      operation.inputs.map Translate.valueType = List.replicate op.arity (valtype_numtype op.input) ∧
      Translate.valueType operation.output = valtype_numtype op.output ∧
      runtime.compiler.lower.FunctionCompiler.op ops before out.core (floatOpcode op) 0#u32 0#u32 0#u128 = .ok (.Ok (),after) ∧
      Numeric.read operation {st.core with pos := next} = .ok (.Ok (),out.core) ∧
      code.read_conversion {st.core with pos := next} operation.input operation.output = .ok (.Ok (),out.core) ∧
      out.core.ctrls = st.core.ctrls ∧ out.core.pos = next ∧
      ∃ values, StackSemantics.NumericEffect p.current.ctrl.polymorphic_base p.current.vals
        operation.inputs operation.output values ∧
        Wasm2.ReaderPost p out.core op.source p.current.ctrl.polymorphic_base values := by
  obtain ⟨sub,operation,hook,subEq,bound,meaning,instruction,inputs,output,encoding,hookEq⟩ :=
    float_saturating_reader_facts ops before out.core op extension
  have same : sub = subopcode := (UScalar.eq_equiv _ _).mpr (subEq.trans subopcodeEq.symm)
  subst sub
  obtain ⟨capacity,run⟩ := profile_scalar_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index 0xfc#u8 before after (by decide) accepted
  rw [code.step_wasm2.saturating _ _ _ _ _ _ _ _ decoded bound] at run
  obtain ⟨callback,read,converted,controls,position,values,numeric,post⟩ :=
    reader_saturating_wasm2 p (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      before after out.core ctx subopcode next operation capacity byte decoded meaning run
  have dispatch := ExtendedNumericHook.dispatch (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before out.core hook
  rw [encoding] at dispatch
  dsimp only at dispatch
  rw [dispatch,hookEq] at callback
  exact ⟨operation,instruction,inputs,output,callback,read,converted,controls,position,values,numeric,instruction ▸ post⟩

end Itasca.Runtime.Compiler

end

/-! ## SaturatingEmissions -/

section

/-!
Emission of saturating conversion instructions.

Main declarations: `reader_emit_saturating_wasm2`. A direct consumer is `Compiler.Body.Reader.Checking.OperationInstructionPrefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_emit_saturating_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (op : SourceMachine.Float.Instruction) (C : context)
    (contextLocalsCode : C.LOCALS = compilerLocals before) (extension : 256 ≤ (floatOpcode op).val)
    (subopcode : U32) (next : Usize)
    (subopcodeEq : subopcode.val = (floatOpcode op).val - 256)
    (decoded : Leb128.Decoded data st.core.pos subopcode next)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 0xfc#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (0xfc#u8) before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.core.pos ∧
    (∃ front values,
      Sequence.stackTypes st.core.vals.val = front ++ List.replicate op.arity (valtype_numtype op.input) ∧
      Wasm2.ReaderPost p out.core op.source p.current.ctrl.polymorphic_base values ∧
      ∃ emitted, TypedLowered before after out.core.vals.val emitted (front ++ [valtype_numtype op.output]) ∧
        ScalarEmission C (front ++ List.replicate op.arity (valtype_numtype op.input))
          op.source [emitted] (front ++ [valtype_numtype op.output])) := by
  obtain ⟨operation,instruction,inputs,output,callback,_,_,_,_,values,effect,post⟩ :=
    reader_float_saturating_wasm2 p ops before after out ctx op extension subopcode next subopcodeEq decoded byte accepted
  have ordinary := compiler_float_ordinary_result ops law before after out.core op (.Ok ()) callback
  have sources := compiler_float_sources ops law before after out.core op callback
  have cursor := compiler_float_cursor ops law before after out.core op callback
  refine ⟨ordinary, sources, cursor, ?_⟩
  rw [monomorphic] at effect
  obtain ⟨old, new⟩ := post.values
  obtain ⟨front, types, oldTypes, concrete, newTypes⟩ := numeric_full_stack_types known old new effect
  rw [inputs] at oldTypes
  rw [output] at newTypes
  rw [oldTypes] at layout
  have lowered := compiler_float_lowered ops law before out.core types front op layout reachable
    concrete newTypes codeFits sourceFits coordinateFits
  rw [callback, WP.spec_ok] at lowered
  obtain ⟨left, right, leftPosition, rightPosition, lower⟩ := lowered rfl
  refine ⟨front, values, oldTypes, post, _, ⟨lower, SourceStack.of_map types concrete newTypes⟩, ?_⟩
  exact ScalarEmission.float front op left right
    (by simpa only [contextLocalsCode] using leftPosition) rightPosition

end Itasca.Runtime.Compiler

end

/-! ## Empty -/

section

/-!
Reader inversion and compiler emission for nop and drop, including exact popped operand correspondence.
-/

/-! ## Reader Wasm2 Drop -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2 Itasca.VisitorTrace

theorem reader_drop_wasm2 {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_DROP)
    (accepted : code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_DROP before =
      .ok (.Ok (), out, after)) :
    ∃ value values, visitor.on_drop before out value = .ok (.Ok (), after) ∧
      code.read_drop st.core = .ok (.Ok value, out) ∧
      StackSemantics.Popped p.current.ctrl.polymorphic_base p.current.vals value values ∧
      Wasm2.ReaderPost p out .DROP p.current.ctrl.polymorphic_base values := by
  rw [dispatch_drop] at accepted
  obtain ⟨value, read, callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
  have effect := p.read_drop byte
  rw [read, WP.spec_ok] at effect
  obtain ⟨values, operands, post⟩ := effect value rfl
  exact ⟨value, values, callback, read, operands, post⟩

end Itasca.Runtime.Compiler

end

/-! ## Reader Empty -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_emit_nop_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (types : List wasm_types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translate.valueType))
    (byte : data.val[p.start.val]'p.inbounds = code.OP_NOP)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_NOP before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.core.pos ∧
    (Wasm2.ReaderPost p out.core .NOP p.current.ctrl.polymorphic_base p.current.vals ∧
      TypedLoweredEmpty before after out.core.vals.val (types.map Translate.valueType) ∧
      LinearEmission (compilerLocals before) (types.map Translate.valueType) .NOP [] (types.map Translate.valueType)) := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals, p.ft.results⟩ index code.OP_NOP before after (by simp only [global_simps]; decide)
    (by simp only [global_simps]; decide) (by simp only [global_simps]; rfl)
    (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨callback, post⟩ := reader_nop_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core byte run
  have vals : out.core.vals.val = st.core.vals.val := post.values.2.trans post.values.1.symm
  have postConcrete : out.core.vals.val = types.map code.StackType.Val := vals.trans concrete
  have lowered := compiler_observe_empty ops law before out.core types _ layout postConcrete
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 1#u16 0#u32 0#u32 0#u128 = _ at callback
  have ordinary := compiler_op1_ordinary_result ops law before after out.core 0#u32 0#u32 0#u128 (.Ok ()) callback
  have sources := compiler_op1_sources ops law before after out.core 0#u32 0#u32 0#u128 callback
  have cursor := compiler_op1_cursor ops law before after out.core 0#u32 0#u32 0#u128 callback
  refine ⟨ordinary, sources, cursor, ?_⟩
  have lowerEq := lower_empty_eq ops before out.core false
  simp only [Bool.false_eq_true, ite_false, ite_true] at lowerEq
  rw [lowerEq] at callback
  rw [callback, WP.spec_ok] at lowered
  exact ⟨post, ⟨lowered rfl, SourceStack.of_map types postConcrete rfl⟩, .nop _⟩

theorem popped_concrete_exact {segment rest : List code.StackType} {value}
    (known : ConcreteStack segment) (popped : StackSemantics.Popped false segment value rest) :
    ∃ ty : wasm_types.ValueType, value = .Val ty ∧ segment = rest ++ [.Val ty] := by
  cases popped with
  | explicit =>
    cases value with
    | Bot => exact False.elim (known .Bot (by simp) rfl)
    | Val raw => exact ⟨raw, rfl, rfl⟩

theorem reader_emit_drop_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (byte : data.val[p.start.val]'p.inbounds = code.OP_DROP)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_DROP before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.core.pos ∧
    (∃ (front : List valtype) (ty : wasm_types.ValueType) (values : List code.StackType),
      Sequence.stackTypes st.core.vals.val = front ++ [Translate.valueType ty] ∧
      Wasm2.ReaderPost p out.core .DROP p.current.ctrl.polymorphic_base values ∧
      TypedLoweredEmpty before after out.core.vals.val front ∧
      LinearEmission (compilerLocals before) (front ++ [Translate.valueType ty]) .DROP [] front) := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals, p.ft.results⟩ index code.OP_DROP before after (by simp only [global_simps]; decide)
    (by simp only [global_simps]; decide) (by simp only [global_simps]; rfl)
    (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨value, values, callback, _, popped, post⟩ := reader_drop_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core byte run
  obtain ⟨old, new⟩ := post.values
  have currentKnown := (concrete_stack_append.mp (old ▸ known)).2
  rw [monomorphic] at popped
  obtain ⟨ty, valueType, segmentShape⟩ := popped_concrete_exact currentKnown popped
  have shape : st.core.vals.val = out.core.vals.val ++ [.Val ty] := by
    rw [old, new, segmentShape, List.append_assoc]
  have afterKnown : ConcreteStack out.core.vals.val := (concrete_stack_append.mp (shape ▸ known)).1
  obtain ⟨types, concrete⟩ := (concrete_stack_iff out.core.vals.val).mp afterKnown
  have beforeTypes : Sequence.stackTypes st.core.vals.val = types.map Translate.valueType ++ [Translate.valueType ty] := by
    simp [shape, concrete, Sequence.stackTypes, List.map_map, Function.comp_def]
  have lowered := compiler_observe_empty ops law before out.core types _ layout concrete
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 26#u16 0#u32 0#u32 0#u128 = _ at callback
  have ordinary := compiler_op26_ordinary_result ops law before after out.core 0#u32 0#u32 0#u128 (.Ok ()) callback
  have sources := compiler_op26_sources ops law before after out.core 0#u32 0#u32 0#u128 callback
  have cursor := compiler_op26_cursor ops law before after out.core 0#u32 0#u32 0#u128 callback
  refine ⟨ordinary, sources, cursor, ?_⟩
  have lowerEq := lower_empty_eq ops before out.core true
  simp only [Bool.false_eq_true, ite_false, ite_true] at lowerEq
  rw [lowerEq] at callback
  rw [callback, WP.spec_ok] at lowered
  exact ⟨types.map Translate.valueType, ty, values, beforeTypes, post, ⟨lowered rfl, SourceStack.of_map types concrete rfl⟩, .drop _ _⟩

end Itasca.Runtime.Compiler

end

end

/-! ## IntegerFacts -/

section

/-!
All non-extension integer instructions use the canonical scalar reader and visitor dispatch table, with exactly the descriptor's operand types.

Main declarations: `integer_reader_facts`. A direct consumer is `Compiler.Body.Reader.Acceptance.ReachedNumericAcceptance`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace SourceMachine.Numeric

/-- All non-extension integer instructions use the canonical scalar reader
and visitor dispatch table, with exactly the descriptor's operand types. -/
theorem integer_reader_facts {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState)
    (op : Instruction) (base : (integerOpcode op).val < 192) :
    ∃ (operation : Numeric.Operation) (hook : NumericHook),
      Numeric.opcodeMeaning (UScalar.cast .U8 (integerOpcode op)) = some operation ∧
      NumericHook.ofOpcode (UScalar.cast .U8 (integerOpcode op)) = some hook ∧
      operation.instruction = op.source ∧
      operation.inputs.map Translate.valueType = List.replicate op.arity (integerType op.input) ∧
      Translate.valueType operation.output = integerType op.output ∧
      invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler (.op state (.numeric hook)) =
        runtime.compiler.lower.FunctionCompiler.op ops compiler state (integerOpcode op) 0#u32 0#u32 0#u128 ∧
      (UScalar.cast .U8 (integerOpcode op)).val ∉ Wasm2.controlOpcodes ∧
      (UScalar.cast .U8 (integerOpcode op)).val ∉ [28, 37, 38, 208, 209, 210, 252, 253] ∧
      Wasm2.NumericExtensions.signMeaning (UScalar.cast .U8 (integerOpcode op)) = none ∧
      UScalar.cast .U8 (integerOpcode op) ≠ code.OP_MISC_PREFIX := by
  cases op with
  | binary ty operator =>
    cases ty <;> cases operator <;> (try (rename_i sign; cases sign)) <;>
      refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, rfl, ?_⟩ <;>
      simp only [global_simps] <;> decide
  | compare ty operator =>
    cases ty <;> cases operator <;> (try (rename_i sign; cases sign)) <;>
      refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, rfl, ?_⟩ <;>
      simp only [global_simps] <;> decide
  | unary ty operator =>
    cases ty <;> cases operator
    all_goals try (norm_num [integerOpcode] at base)
    all_goals
      refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, rfl, ?_⟩
      simp only [global_simps]
      decide
  | eqz ty =>
    cases ty <;>
      refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, rfl, ?_⟩ <;>
      simp only [global_simps] <;> decide
  | conversion operator =>
    cases operator <;>
      refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, rfl, ?_⟩ <;>
      simp only [global_simps] <;> decide
end Itasca.Runtime.Compiler

end

/-! ## NumericEmissions -/

section

/-!
Integer opcode emission from accepted reader steps.

Main declarations: `reader_emit_numeric_wasm2`. A direct consumer is `Compiler.Body.Reader.Checking.OperationInstructionPrefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_emit_numeric_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (op : SourceMachine.Numeric.Instruction) (baseOpcode : (integerOpcode op).val < 192)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.core.pos ∧
    (∃ front values,
      Sequence.stackTypes st.core.vals.val = front ++ List.replicate op.arity (integerType op.input) ∧
      Wasm2.ReaderPost p out.core op.source p.current.ctrl.polymorphic_base values ∧
      ∃ emitted, TypedLowered before after out.core.vals.val emitted (front ++ [integerType op.output]) ∧
        LinearEmission (compilerLocals before) (front ++ List.replicate op.arity (integerType op.input))
          op.source [emitted] (front ++ [integerType op.output])) := by
  obtain ⟨operation, hook, meaning, handler, instruction, inputs, output,
    hookEq, ordinary, base, sign, misc⟩ := integer_reader_facts ops before out.core op baseOpcode
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals, p.ft.results⟩ index _ before after ordinary base sign misc contextLocals accepted
  obtain ⟨callback, _, _, _, values, effect, post⟩ := reader_numeric_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core _ operation hook
    capacity byte meaning handler run
  rw [hookEq] at callback
  have ordinary := compiler_numeric_ordinary_result ops law before after out.core op (.Ok ()) callback
  have sources := compiler_numeric_sources ops law before after out.core op callback
  have cursor := compiler_numeric_cursor ops law before after out.core op callback
  refine ⟨ordinary, sources, cursor, ?_⟩
  rw [monomorphic] at effect
  obtain ⟨old, new⟩ := post.values
  obtain ⟨front, types, oldTypes, concrete, newTypes⟩ := numeric_full_stack_types known old new effect
  rw [inputs] at oldTypes
  rw [output] at newTypes
  rw [instruction] at post
  rw [oldTypes] at layout
  have lowered := compiler_numeric_lowered ops law before out.core types front op layout reachable
    concrete newTypes codeFits sourceFits coordinateFits
  rw [callback, WP.spec_ok] at lowered
  obtain ⟨left, right, leftPosition, rightPosition, lower⟩ := lowered rfl
  refine ⟨front, values, oldTypes, post, _, ⟨lower, SourceStack.of_map types concrete newTypes⟩, ?_⟩
  exact LinearEmission.numeric front op left right
    leftPosition rightPosition

end Itasca.Runtime.Compiler

end

/-! ## SelectTypes -/

section

/-!
The full operand-stack types of untyped select.

Main declarations: `select_full_stack_types`. A direct consumer is `Compiler.Body.Reader.Acceptance.ReachedSimpleAcceptance`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem select_full_stack_types {before after outer segment result : List code.StackType} {selected}
    (known : ConcreteStack before) (old : before = outer ++ segment) (new : after = outer ++ result)
    (effect : StackSemantics.SelectEffect false segment selected result) :
    ∃ (ty : wasm_types.ValueType) (front : List valtype) (types : List Itasca.wasm_types.ValueType),
      selected = .Val ty ∧
      Sequence.stackTypes before = front ++ [Translate.valueType ty, Translate.valueType ty, .I32] ∧
      after = types.map code.StackType.Val ∧
      types.map Translate.valueType = front ++ [Translate.valueType ty] := by
  have both := concrete_stack_append.mp (old ▸ known)
  have selectedKnown := (concrete_select_effect both.2 effect).2
  cases selected with
  | Bot => exact False.elim (selectedKnown rfl)
  | Val ty =>
    have numeric : StackSemantics.NumericEffect false segment [ty, ty, .I32] ty result := by
      obtain ⟨_, rest, rfl, transfer⟩ := effect
      exact ⟨rest, rfl, by simpa [StackSemantics.selectedType, Translate.valueType] using transfer⟩
    obtain ⟨front, types, prior, concrete, output⟩ := numeric_full_stack_types known old new numeric
    exact ⟨ty, front, types, rfl, by simpa [Translate.valueType] using prior, concrete, output⟩
end Itasca.Runtime.Compiler

end

/-! ## SelectEmissions -/

section

/-!
Reader inversion and compiler emission for untyped select.
-/

/-! ## Reader Wasm2 Select -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2 Itasca.VisitorTrace

theorem reader_select_wasm2 {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 27#u8)
    (accepted : code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_SELECT before =
      .ok (.Ok (), out, after)) :
    ∃ selected values, visitor.on_select before out selected = .ok (.Ok (), after) ∧
      code.read_select st.core = .ok (.Ok selected, out) ∧
      StackSemantics.SelectEffect p.current.ctrl.polymorphic_base p.current.vals selected values ∧
      Wasm2.ReaderPost p out (.SELECT none) p.current.ctrl.polymorphic_base values := by
  rw [code.step_select.dispatch] at accepted
  obtain ⟨selected, read, callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
  have effect := p.read_select capacity (by simpa [global_simps] using byte)
  rw [read, WP.spec_ok] at effect
  obtain ⟨values, operands, post⟩ := effect selected rfl
  exact ⟨selected, values, callback, read, operands, post⟩

end Itasca.Runtime.Compiler

end

/-! ## Reader Select Emissions -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_emit_select_wasm2 {data env locals typeIndex st}
    (p : Wasm2.Pending data env locals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (C : context) (localsMatch : compilerLocals before = C.LOCALS)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 27#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex code.OP_SELECT before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧ after.next_source = out.core.pos ∧
    ∃ (ty : Itasca.wasm_types.ValueType) (front : List valtype) (values : List code.StackType),
      Sequence.stackTypes st.core.vals.val = front ++ [Translate.valueType ty, Translate.valueType ty, .I32] ∧
      Wasm2.ReaderPost p out.core (.SELECT none) p.current.ctrl.polymorphic_base values ∧
      ∃ emitted, TypedLowered before after out.core.vals.val emitted (front ++ [Translate.valueType ty]) ∧
        ScalarEmission C (front ++ [Translate.valueType ty, Translate.valueType ty, .I32]) (.SELECT none)
          [emitted] (front ++ [Translate.valueType ty]) := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals, p.ft.results⟩ typeIndex code.OP_SELECT before after (by simp only [global_simps]; decide)
    (by simp only [global_simps]; decide) (by simp only [global_simps]; rfl)
    (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨selected, values, callback, read, effect, post⟩ := reader_select_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity byte run
  rw [monomorphic] at effect
  obtain ⟨old, new⟩ := post.values
  obtain ⟨ty, front, types, selectedEq, beforeTypes, concrete, output⟩ := select_full_stack_types known old new effect
  rw [beforeTypes] at layout
  have lowered := compiler_select_emission ops law before out.core types C front (Translate.valueType ty)
    localsMatch layout reachable concrete output codeFits sourceFits coordinateFits
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 27#u16 0#u32 0#u32 0#u128 = _ at callback
  have ordinary := compiler_core_ordinary_result ops law before after out.core (.select false) (.Ok ()) callback
  have sources := compiler_core_sources ops law before after out.core (.select false) callback
  have cursor := compiler_core_cursor ops law before after out.core (.select false) callback
  rw [callback, WP.spec_ok] at lowered
  obtain ⟨emitted, lower, emission⟩ := lowered rfl
  exact ⟨ordinary, sources, cursor, ty, front, values, beforeTypes, post, emitted,
    ⟨lower, SourceStack.of_map types concrete output⟩, emission⟩
end Itasca.Runtime.Compiler

end

end

/-! ## SignEmissions -/

section

/-!
Emission of integer sign-extension instructions.

Main declarations: `reader_emit_sign_wasm2`. A direct consumer is `Compiler.Body.Reader.Checking.OperationInstructionPrefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_emit_sign_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (op : SourceMachine.Numeric.Instruction) (extension : 192 ≤ (integerOpcode op).val)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.core.pos ∧
    (∃ front values,
      Sequence.stackTypes st.core.vals.val = front ++ List.replicate op.arity (integerType op.input) ∧
      Wasm2.ReaderPost p out.core op.source p.current.ctrl.polymorphic_base values ∧
      ∃ emitted, TypedLowered before after out.core.vals.val emitted (front ++ [integerType op.output]) ∧
        LinearEmission (compilerLocals before) (front ++ List.replicate op.arity (integerType op.input))
          op.source [emitted] (front ++ [integerType op.output])) := by
  obtain ⟨operation, instruction, inputs, output, callback, read, converted,
    controls, position, values, effect, post⟩ :=
    reader_integer_sign_wasm2 p ops before after out ctx op extension byte accepted
  have ordinary := compiler_numeric_ordinary_result ops law before after out.core op (.Ok ()) callback
  have sources := compiler_numeric_sources ops law before after out.core op callback
  have cursor := compiler_numeric_cursor ops law before after out.core op callback
  refine ⟨ordinary, sources, cursor, ?_⟩
  rw [monomorphic] at effect
  obtain ⟨old, new⟩ := post.values
  obtain ⟨front, types, oldTypes, concrete, newTypes⟩ := numeric_full_stack_types known old new effect
  rw [inputs] at oldTypes
  rw [output] at newTypes
  rw [oldTypes] at layout
  have lowered := compiler_numeric_lowered ops law before out.core types front op layout reachable
    concrete newTypes codeFits sourceFits coordinateFits
  rw [callback, WP.spec_ok] at lowered
  obtain ⟨left, right, leftPosition, rightPosition, lower⟩ := lowered rfl
  refine ⟨front, values, oldTypes, post, _, ⟨lower, SourceStack.of_map types concrete newTypes⟩, ?_⟩
  exact LinearEmission.numeric front op left right
    leftPosition rightPosition

end Itasca.Runtime.Compiler

end

/-! ## Unreachable -/

section

/-!
The source effect of an accepted unreachable reader step.

Main declarations: `reader_unreachable_wasm2`. A direct consumer is `Compiler.Body.Reader.Control.TerminalInstructionPrefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

theorem reader_unreachable_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_UNREACHABLE)
    (accepted : code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_UNREACHABLE before =
      .ok (.Ok (), out, after)) :
    visitor.on_unreachable before out = .ok (.Ok (), after) ∧
      out.vals.val = st.core.vals.val.take p.current.ctrl.value_stack_base.val ∧
      Wasm2.ReaderPost p out .UNREACHABLE true [] := by
  rw [dispatch_unreachable] at accepted
  obtain ⟨unit, read, callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
  cases unit
  have effect := p.read_unreachable byte
  rw [read, WP.spec_ok] at effect
  exact ⟨callback, effect.2⟩

end Itasca.Runtime.Compiler

end
