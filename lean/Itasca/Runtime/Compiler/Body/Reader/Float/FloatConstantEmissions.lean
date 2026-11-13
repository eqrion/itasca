import Itasca.Runtime.Compiler.Local.Lowering.Float.FloatLowering
import Itasca.Runtime.Compiler.Body.Reader.Stacks.Values
import Itasca.Runtime.Compiler.Body.Reader.Replay.BulkAndSaturatingAcceptance
import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericLowering
import Itasca.Runtime.Compiler.Local.Relations.Prefix.SuspendedPrefix
import Itasca.Runtime.Compiler.Local.Lowering.Float.FloatEncoding
import Itasca.Runtime.Compiler.Body.Source.TypedLowering
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Wasm2.Scalar.IndexReader
import Itasca.Runtime.Compiler.Body.Reader.Replay.Post
import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty
import Itasca.Runtime.Compiler.Local.Lowering.Literal.LiteralSources
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Spec.TypingInversion

/-!
Sections, each formerly its own module: FloatFacts, FloatEmissions, FloatConstant, FloatConstantLowering, FloatConstantEmissions.
-/

/-! ## FloatFacts -/

section

/-!
All base float instructions use the canonical scalar reader and visitor dispatch table, with exactly the descriptor's operand types.

Main declarations: `float_reader_facts`. A direct consumer is `Compiler.Body.Reader.Acceptance.ReachedNumericAcceptance`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace SourceMachine.Float

/-- All base float instructions use the canonical scalar reader
and visitor dispatch table, with exactly the descriptor's operand types. -/
theorem float_reader_facts {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState)
    (op : Instruction) (base : (floatOpcode op).val < 256) :
    ∃ (operation : Numeric.Operation) (hook : NumericHook),
      Numeric.opcodeMeaning (UScalar.cast .U8 (floatOpcode op)) = some operation ∧
      NumericHook.ofOpcode (UScalar.cast .U8 (floatOpcode op)) = some hook ∧
      operation.instruction = op.source ∧
      operation.inputs.map Translate.valueType = List.replicate op.arity (valtype_numtype op.input) ∧
      Translate.valueType operation.output = valtype_numtype op.output ∧
      invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler (.op state (.numeric hook)) =
        runtime.compiler.lower.FunctionCompiler.op ops compiler state (floatOpcode op) 0#u32 0#u32 0#u128 ∧
      (UScalar.cast .U8 (floatOpcode op)).val ∉ Wasm2.controlOpcodes ∧
      (UScalar.cast .U8 (floatOpcode op)).val ∉ [28, 37, 38, 208, 209, 210, 252, 253] ∧
      Wasm2.NumericExtensions.signMeaning (UScalar.cast .U8 (floatOpcode op)) = none ∧
      UScalar.cast .U8 (floatOpcode op) ≠ code.OP_MISC_PREFIX := by
  cases op with
  | unary ty operator => cases ty <;> cases operator <;> (first | (solve | norm_num [floatOpcode,SourceMachine.Float.Instruction.opcode,SourceMachine.Float.signIndex] at base) | (refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, rfl, ?_⟩; simp only [global_simps]; decide))
  | binary ty operator => cases ty <;> cases operator <;> (first | (solve | norm_num [floatOpcode,SourceMachine.Float.Instruction.opcode,SourceMachine.Float.signIndex] at base) | (refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, rfl, ?_⟩; simp only [global_simps]; decide))
  | compare ty operator => cases ty <;> cases operator <;> (first | (solve | norm_num [floatOpcode,SourceMachine.Float.Instruction.opcode,SourceMachine.Float.signIndex] at base) | (refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, rfl, ?_⟩; simp only [global_simps]; decide))
  | convert source target sign => cases source <;> cases target <;> cases sign <;> (first | (solve | norm_num [floatOpcode,SourceMachine.Float.Instruction.opcode,SourceMachine.Float.signIndex] at base) | (refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, rfl, ?_⟩; simp only [global_simps]; decide))
  | truncate source target sign saturating => cases source <;> cases target <;> cases sign <;> cases saturating <;> (first | (solve | norm_num [floatOpcode,SourceMachine.Float.Instruction.opcode,SourceMachine.Float.signIndex] at base) | (refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, rfl, ?_⟩; simp only [global_simps]; decide))
  | reinterpretFloat source => cases source <;> (first | (solve | norm_num [floatOpcode,SourceMachine.Float.Instruction.opcode,SourceMachine.Float.signIndex] at base) | (refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, rfl, ?_⟩; simp only [global_simps]; decide))
  | reinterpretInt source => cases source <;> (first | (solve | norm_num [floatOpcode,SourceMachine.Float.Instruction.opcode,SourceMachine.Float.signIndex] at base) | (refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, rfl, ?_⟩; simp only [global_simps]; decide))
  | promote | demote => skip <;> (first | (solve | norm_num [floatOpcode,SourceMachine.Float.Instruction.opcode,SourceMachine.Float.signIndex] at base) | (refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, rfl, ?_⟩; simp only [global_simps]; decide))
end Itasca.Runtime.Compiler

end

/-! ## FloatEmissions -/

section

/-!
Floating-point operation emission from accepted reader steps.

Main declarations: `reader_emit_float_wasm2`. A direct consumer is `Compiler.Body.Reader.Float.Compilation`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_emit_float_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (op : SourceMachine.Float.Instruction) (C : context)
    (contextLocalsCode : C.LOCALS = compilerLocals before) (baseOpcode : (floatOpcode op).val < 256)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (floatOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (UScalar.cast .U8 (floatOpcode op)) before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.core.pos ∧
    (∃ front values,
      Sequence.stackTypes st.core.vals.val = front ++ List.replicate op.arity (valtype_numtype op.input) ∧
      Wasm2.ReaderPost p out.core op.source p.current.ctrl.polymorphic_base values ∧
      ∃ emitted, TypedLowered before after out.core.vals.val emitted (front ++ [valtype_numtype op.output]) ∧
        ScalarEmission C (front ++ List.replicate op.arity (valtype_numtype op.input))
          op.source [emitted] (front ++ [valtype_numtype op.output])) := by
  obtain ⟨operation, hook, meaning, handler, instruction, inputs, output,
    hookEq, ordinary, base, sign, misc⟩ := float_reader_facts ops before out.core op baseOpcode
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals, p.ft.results⟩ index _ before after ordinary base sign misc contextLocals accepted
  obtain ⟨callback, _, _, _, values, effect, post⟩ := reader_numeric_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core _ operation hook
    capacity byte meaning handler run
  rw [hookEq] at callback
  have ordinary := compiler_float_ordinary_result ops law before after out.core op (.Ok ()) callback
  have sources := compiler_float_sources ops law before after out.core op callback
  have cursor := compiler_float_cursor ops law before after out.core op callback
  refine ⟨ordinary, sources, cursor, ?_⟩
  rw [monomorphic] at effect
  obtain ⟨old, new⟩ := post.values
  obtain ⟨front, types, oldTypes, concrete, newTypes⟩ := numeric_full_stack_types known old new effect
  rw [inputs] at oldTypes
  rw [output] at newTypes
  rw [instruction] at post
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

/-! ## FloatConstant -/

section

/-!
Reader inversion for 32-bit and 64-bit floating-point constants.

Main declarations: `reader_f32_const_wasm2` and `reader_f64_const_wasm2`. A direct consumer is `Compiler.Body.Reader.Float.ConstantPrefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
open Itasca.Wasm1 in
open Itasca.Wasm2 in
theorem reader_f32_const_wasm2 {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_F32_CONST)
    (accepted : code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_F32_CONST before =
      .ok (.Ok (), out, after)) :
    ∃ value, visitor.on_f32_const before out value = .ok (.Ok (), after) ∧
      code.read_f32_const st.core data = .ok (.Ok value, out) ∧
      out.vals.val = st.core.vals.val ++ [.Val .F32] ∧
      Wasm2.ReaderPost p out (ScalarConst.f32 value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [code.StackType.Val wasm_types.ValueType.F32]) := by
  rw [dispatch_f32_const] at accepted
  obtain ⟨value, read, callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
  have effect := p.read_f32_const capacity byte
  rw [read, WP.spec_ok] at effect
  obtain ⟨values, post⟩ := effect value rfl
  exact ⟨value, callback, read, values, post⟩

open Itasca.Wasm2 in
theorem reader_f64_const_wasm2 {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_F64_CONST)
    (accepted : code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_F64_CONST before =
      .ok (.Ok (), out, after)) :
    ∃ value, visitor.on_f64_const before out value = .ok (.Ok (), after) ∧
      code.read_f64_const st.core data = .ok (.Ok value, out) ∧
      out.vals.val = st.core.vals.val ++ [.Val .F64] ∧
      Wasm2.ReaderPost p out (ScalarConst.f64 value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [code.StackType.Val wasm_types.ValueType.F64]) := by
  rw [dispatch_f64_const] at accepted
  obtain ⟨value, read, callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
  have effect := p.read_f64_const capacity byte
  rw [read, WP.spec_ok] at effect
  obtain ⟨values, post⟩ := effect value rfl
  exact ⟨value, callback, read, values, post⟩

end Itasca.Runtime.Compiler

end

/-! ## FloatConstantLowering -/

section

/-!
Compiler callbacks for floating-point constants.

Main declarations: `callback_float32_eq` and `callback_float64`. A direct consumer is `Compiler.Body.Reader.Float.ConstantPrefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

theorem callback_float32_eq {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) (value : U32) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f32_const ops compiler state value =
      runtime.compiler.lower.FunctionCompiler.op ops compiler state 65#u16 0#u32 0#u32 (UScalar.cast .U128 value) := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f32_const,lift,bind_ok]
  unfold runtime.compiler.lower.FunctionCompiler.op
  split <;> rfl

theorem callback_float64_eq {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) (value : U64) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f64_const ops compiler state value =
      runtime.compiler.lower.FunctionCompiler.op ops compiler state 66#u16 0#u32 0#u32 (UScalar.cast .U128 value) := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f64_const,lift,bind_ok]
  unfold runtime.compiler.lower.FunctionCompiler.op
  split <;> rfl

@[step] theorem callback_float32 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.wasm_types.ValueType)
    (before : List valtype) (value : U32)
    (layout : CompilerLayout compiler before) (reachable : compiler.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f32_const ops compiler state value ⦃ out =>
      out.1 = .Ok () → Lowered compiler out.2
        (.Const32 compiler.height value) (types.map Itasca.Translate.valueType) ⦄ := by
  rw [callback_float32_eq]
  have bits : UScalar.cast .U32 (UScalar.cast .U128 value) =
      value := by
    apply UScalar.eq_of_val_eq
    simp only [UScalar.cast_val_eq]
    scalar_tac
  simpa only [bits] using lower_const32 ops law compiler state types before
    (UScalar.cast .U128 value) layout reachable concrete
    codeFits sourceFits coordinateFits

@[step] theorem callback_float64 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.wasm_types.ValueType)
    (before : List valtype) (value : U64)
    (layout : CompilerLayout compiler before) (reachable : compiler.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f64_const ops compiler state value ⦃ out =>
      out.1 = .Ok () → Lowered compiler out.2
        (.Const64 compiler.height value) (types.map Itasca.Translate.valueType) ⦄ := by
  rw [callback_float64_eq]
  have bits : UScalar.cast .U64 (UScalar.cast .U128 value) =
      value := by
    apply UScalar.eq_of_val_eq
    simp only [UScalar.cast_val_eq]
    scalar_tac
  simpa only [bits] using lower_const64 ops law compiler state types before
    (UScalar.cast .U128 value) layout reachable concrete
    codeFits sourceFits coordinateFits

end Itasca.Runtime.Compiler

end

/-! ## FloatConstantEmissions -/

section

/-!
Floating-point constant encoding and compiler emission from accepted reader steps.
-/

/-! ## Reader Float Constant Encoding -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
theorem scalar_float_value_32 (bits : U32) :
    SpecExt.Builtins.floatOfBits 32 bits.val = ScalarConst.floatValue 23 8 bits.val := by
  have bound : bits.val < 2^32 := by scalar_tac
  have sign : (bits.val / 2^31) % 2 = 0 ↔ bits.val < 2^31 := by omega
  norm_num at sign
  simp [SpecExt.Builtins.floatOfBits, ScalarConst.floatValue, fun_M, E, signif, expon,
    SpecExt.Builtins.floatBias, sign]

theorem scalar_float_value_64 (bits : U64) :
    SpecExt.Builtins.floatOfBits 64 bits.val = ScalarConst.floatValue 52 11 bits.val := by
  have bound : bits.val < 2^64 := by scalar_tac
  have sign : (bits.val / 2^63) % 2 = 0 ↔ bits.val < 2^63 := by omega
  norm_num at sign
  simp [SpecExt.Builtins.floatOfBits, ScalarConst.floatValue, fun_M, E, signif, expon,
    SpecExt.Builtins.floatBias, sign]


end Itasca.Runtime.Compiler

end

/-! ## Reader Float Constant Emissions -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
/-- An actual successful constant reader and compiler callback extends the
retained code prefix and the supplied source zipper together. -/
theorem reader_emit_float32_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A)
    (C : context) (localTypes : C.LOCALS = compilerLocals before) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (types : List wasm_types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translate.valueType))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_F32_CONST)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_F32_CONST before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.core.pos ∧
    (∃ value,
      Wasm2.ReaderPost p out.core (ScalarConst.f32 value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [.Val .F32]) ∧
      ∃ emitted, TypedLowered before after out.core.vals.val emitted (types.map Translate.valueType ++ [.F32]) ∧
        ScalarEmission C (types.map Translate.valueType) (ScalarConst.f32 value) [emitted]
          (types.map Translate.valueType ++ [.F32])) := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals, p.ft.results⟩ index code.OP_F32_CONST before after (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨value, callback, _, vals, post⟩ := reader_f32_const_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity byte run
  have postConcrete : out.core.vals.val = (types ++ [Itasca.wasm_types.ValueType.F32]).map code.StackType.Val := by
    simp [vals, concrete]
  have lowered := callback_float32 ops law before out.core (types ++ [Itasca.wasm_types.ValueType.F32])
    (types.map Translate.valueType) value layout reachable postConcrete codeFits sourceFits coordinateFits
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f32_const ops before out.core value = _ at callback
  rw [callback_float32_eq] at callback
  have ordinary := compiler_op65_ordinary_result ops law before after out.core 0#u32 0#u32 (UScalar.cast .U128 value) (.Ok ()) callback
  have sources := compiler_op65_sources ops law before after out.core 0#u32 0#u32 (UScalar.cast .U128 value) callback
  have cursor := compiler_op65_cursor ops law before after out.core 0#u32 0#u32 (UScalar.cast .U128 value) callback
  refine ⟨ordinary, sources, cursor, ?_⟩
  rw [callback_float32_eq, callback, WP.spec_ok] at lowered
  have lower := lowered rfl
  simp only [List.map_append, List.map_cons, List.map_nil, Translate.valueType] at lower
  have instruction : ScalarConst.f32 value =
      .CONST .F32 (.mk_num__1 .F32 (SpecExt.Builtins.floatOfBits 32 value.val)) := by rw [scalar_float_value_32]; rfl
  refine ⟨value, post, _, ⟨lower, SourceStack.of_map (types ++ [.F32]) postConcrete (by simp [Translate.valueType])⟩, ?_⟩
  rw [instruction]
  apply ScalarEmission.float32
  simpa only [localTypes] using layout.height

/-- An actual successful constant reader and compiler callback extends the
retained code prefix and the supplied source zipper together. -/
theorem reader_emit_float64_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A)
    (C : context) (localTypes : C.LOCALS = compilerLocals before) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (types : List wasm_types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translate.valueType))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_F64_CONST)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_F64_CONST before = .ok (.Ok (), out, after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧
    after.next_source = out.core.pos ∧
    (∃ value,
      Wasm2.ReaderPost p out.core (ScalarConst.f64 value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [.Val .F64]) ∧
      ∃ emitted, TypedLowered before after out.core.vals.val emitted (types.map Translate.valueType ++ [.F64]) ∧
        ScalarEmission C (types.map Translate.valueType) (ScalarConst.f64 value) [emitted]
          (types.map Translate.valueType ++ [.F64])) := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals, p.ft.results⟩ index code.OP_F64_CONST before after (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨value, callback, _, vals, post⟩ := reader_f64_const_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity byte run
  have postConcrete : out.core.vals.val = (types ++ [Itasca.wasm_types.ValueType.F64]).map code.StackType.Val := by
    simp [vals, concrete]
  have lowered := callback_float64 ops law before out.core (types ++ [Itasca.wasm_types.ValueType.F64])
    (types.map Translate.valueType) value layout reachable postConcrete codeFits sourceFits coordinateFits
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f64_const ops before out.core value = _ at callback
  rw [callback_float64_eq] at callback
  have ordinary := compiler_op66_ordinary_result ops law before after out.core 0#u32 0#u32 (UScalar.cast .U128 value) (.Ok ()) callback
  have sources := compiler_op66_sources ops law before after out.core 0#u32 0#u32 (UScalar.cast .U128 value) callback
  have cursor := compiler_op66_cursor ops law before after out.core 0#u32 0#u32 (UScalar.cast .U128 value) callback
  refine ⟨ordinary, sources, cursor, ?_⟩
  rw [callback_float64_eq, callback, WP.spec_ok] at lowered
  have lower := lowered rfl
  simp only [List.map_append, List.map_cons, List.map_nil, Translate.valueType] at lower
  have instruction : ScalarConst.f64 value =
      .CONST .F64 (.mk_num__1 .F64 (SpecExt.Builtins.floatOfBits 64 value.val)) := by rw [scalar_float_value_64]; rfl
  refine ⟨value, post, _, ⟨lower, SourceStack.of_map (types ++ [.F64]) postConcrete (by simp [Translate.valueType])⟩, ?_⟩
  rw [instruction]
  apply ScalarEmission.float64
  simpa only [localTypes] using layout.height

end Itasca.Runtime.Compiler

end

end
