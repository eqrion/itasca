import Itasca.Runtime.Compiler.Local.Lowering.Emission.OpEquations
import Itasca.Runtime.Compiler.Local.Callbacks.CallbackEquations
import Itasca.Runtime.Compiler.Local.Lowering.Float.LoweringAndEffects
import Itasca.Runtime.Compiler.Body.Reader.StackValues
import Itasca.Runtime.Compiler.Body.Reader.Replay.ReaderCompilerState
import Itasca.Runtime.Compiler.Local.Lowering.Integer.Lowering
import Itasca.Runtime.Compiler.Local.Relations.Prefix.SuspendedPrefix
import Itasca.Runtime.Compiler.Body.CapacityTrace
import Itasca.Runtime.Compiler.Local.Definitions
import Itasca.Body.Scalar.Readers
import Itasca.Runtime.Compiler.Body.Reader.Replay.Post
import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty
import Itasca.Runtime.Compiler.Local.Lowering.Literal.SourceEffects
import Itasca.Runtime.Compiler.Local.Callbacks.MetadataPreservation
import Itasca.Spec.Typing

/-! ## FloatFacts -/

section

/-!
All base float instructions use the canonical scalar reader and visitor dispatch table, with exactly the descriptor's operand types.

Main declarations: `float_reader_facts`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace SourceMachine.Float

/-- All base float instructions use the canonical scalar reader
and visitor dispatch table, with exactly the descriptor's operand types. -/
theorem float_reader_facts {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState)
    (op : Instruction) (base : (floatOpcode op).val < 256) :
    ∃ (operation : Body.Numeric.Operation) (hook : NumericHook),
      Body.Numeric.opcodeMeaning (UScalar.cast .U8 (floatOpcode op)) = some operation ∧
      NumericHook.ofOpcode (UScalar.cast .U8 (floatOpcode op)) = some hook ∧
      operation.instruction = op.source ∧
      operation.inputs.map Translation.valueType = List.replicate op.arity (valtype_numtype op.input) ∧
      Translation.valueType operation.output = valtype_numtype op.output ∧
      invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler (.op state (.numeric hook)) =
        runtime.compiler.lower.FunctionCompiler.op ops compiler state (floatOpcode op) 0#u32 0#u32 0#u128 ∧
      (UScalar.cast .U8 (floatOpcode op)).val ∉ Body.controlOpcodes ∧
      (UScalar.cast .U8 (floatOpcode op)).val ∉ [28, 37, 38, 208, 209, 210, 252, 253] ∧
      Body.NumericExtensions.signMeaning (UScalar.cast .U8 (floatOpcode op)) = none ∧
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
end Itasca.Compiler

end

/-! ## FloatEmissions -/

section

/-!
Floating-point operation emission from accepted reader steps.

Main declarations: `reader_emit_float`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_emit_float {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (op : SourceMachine.Float.Instruction) (C : context)
    (contextLocalsCode : C.LOCALS = compilerLocals before) (baseOpcode : (floatOpcode op).val < 256)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Body.Stack.stackTypes st.core.vals.val))
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
      Body.Stack.stackTypes st.core.vals.val = front ++ List.replicate op.arity (valtype_numtype op.input) ∧
      Body.ReaderPost p out.core op.source p.current.ctrl.polymorphic_base values ∧
      ∃ emitted, TypedLowered before after out.core.vals.val emitted (front ++ [valtype_numtype op.output]) ∧
        ScalarEmission C (front ++ List.replicate op.arity (valtype_numtype op.input))
          op.source [emitted] (front ++ [valtype_numtype op.output])) := by
  obtain ⟨operation, hook, meaning, handler, instruction, inputs, output,
    hookEq, ordinary, base, sign, misc⟩ := float_reader_facts ops before out.core op baseOpcode
  obtain ⟨capacity, run⟩ := base_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals, p.ft.results⟩ index _ before after ordinary base sign misc contextLocals accepted
  obtain ⟨callback, _, _, _, values, effect, post⟩ := reader_numeric p
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

end Itasca.Compiler

end

/-! ## FloatConstant -/

section

/-!
Reader inversion for 32-bit and 64-bit floating-point constants.

Main declarations: `reader_f32_const` and `reader_f64_const`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace
open Itasca.Body.Scalar in
open Itasca.Body in
theorem reader_f32_const {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_F32_CONST)
    (accepted : code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_F32_CONST before =
      .ok (.Ok (), out, after)) :
    ∃ value, visitor.on_f32_const before out value = .ok (.Ok (), after) ∧
      code.read_f32_const st.core data = .ok (.Ok value, out) ∧
      out.vals.val = st.core.vals.val ++ [.Val .F32] ∧
      Body.ReaderPost p out (Spec.Constants.f32 value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [code.StackType.Val wasm_types.ValueType.F32]) := by
  rw [dispatch_f32_const] at accepted
  obtain ⟨value, read, callback⟩ := Visitor.Core.run.accepted _ _ _ _ _ accepted
  have effect := p.read_f32_const capacity byte
  rw [read, WP.spec_ok] at effect
  obtain ⟨values, post⟩ := effect value rfl
  exact ⟨value, callback, read, values, post⟩

open Itasca.Body in
theorem reader_f64_const {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_F64_CONST)
    (accepted : code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_F64_CONST before =
      .ok (.Ok (), out, after)) :
    ∃ value, visitor.on_f64_const before out value = .ok (.Ok (), after) ∧
      code.read_f64_const st.core data = .ok (.Ok value, out) ∧
      out.vals.val = st.core.vals.val ++ [.Val .F64] ∧
      Body.ReaderPost p out (Spec.Constants.f64 value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [code.StackType.Val wasm_types.ValueType.F64]) := by
  rw [dispatch_f64_const] at accepted
  obtain ⟨value, read, callback⟩ := Visitor.Core.run.accepted _ _ _ _ _ accepted
  have effect := p.read_f64_const capacity byte
  rw [read, WP.spec_ok] at effect
  obtain ⟨values, post⟩ := effect value rfl
  exact ⟨value, callback, read, values, post⟩

end Itasca.Compiler

end

/-! ## FloatConstantLowering -/

section

/-!
Compiler callbacks for floating-point constants.

Main declarations: `callback_float32_eq` and `callback_float64`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

theorem callback_float32_eq {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) (value : U32) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f32_const ops compiler state value =
      runtime.compiler.lower.FunctionCompiler.op ops compiler state 65#u16 0#u32 0#u32 (UScalar.cast .U128 value) := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f32_const.eq,lift,bind_ok]
  by_cases live : compiler.reachable = true
  · rw [runtime.compiler.lower.FunctionCompiler.op.f32_const _ _ _ _ _ _ live,
      runtime.compiler.lower.FunctionCompiler.op.i32_const _ _ _ _ _ _ live]
  · simp only [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _
      (Bool.eq_false_of_not_eq_true live)]

theorem callback_float64_eq {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) (value : U64) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f64_const ops compiler state value =
      runtime.compiler.lower.FunctionCompiler.op ops compiler state 66#u16 0#u32 0#u32 (UScalar.cast .U128 value) := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f64_const.eq,lift,bind_ok]
  by_cases live : compiler.reachable = true
  · rw [runtime.compiler.lower.FunctionCompiler.op.f64_const _ _ _ _ _ _ live,
      runtime.compiler.lower.FunctionCompiler.op.i64_const _ _ _ _ _ _ live]
  · simp only [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _
      (Bool.eq_false_of_not_eq_true live)]

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
        (.Const32 compiler.height value) (types.map Itasca.Translation.valueType) ⦄ := by
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
        (.Const64 compiler.height value) (types.map Itasca.Translation.valueType) ⦄ := by
  rw [callback_float64_eq]
  have bits : UScalar.cast .U64 (UScalar.cast .U128 value) =
      value := by
    apply UScalar.eq_of_val_eq
    simp only [UScalar.cast_val_eq]
    scalar_tac
  simpa only [bits] using lower_const64 ops law compiler state types before
    (UScalar.cast .U128 value) layout reachable concrete
    codeFits sourceFits coordinateFits

end Itasca.Compiler

end

/-! ## FloatConstantEmissions -/

section

/-!
Floating-point constant encoding and compiler emission from accepted reader steps.
-/

/-! ## Reader Float Constant Encoding -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
theorem scalar_float_value_32 (bits : U32) :
    SpecExt.Builtins.floatOfBits 32 bits.val = Spec.Constants.floatValue 23 8 bits.val := by
  have bound : bits.val < 2^32 := by scalar_tac
  have sign : (bits.val / 2^31) % 2 = 0 ↔ bits.val < 2^31 := by omega
  norm_num at sign
  simp [SpecExt.Builtins.floatOfBits, Spec.Constants.floatValue, fun_M, E, signif, expon,
    SpecExt.Builtins.floatBias, sign]

theorem scalar_float_value_64 (bits : U64) :
    SpecExt.Builtins.floatOfBits 64 bits.val = Spec.Constants.floatValue 52 11 bits.val := by
  have bound : bits.val < 2^64 := by scalar_tac
  have sign : (bits.val / 2^63) % 2 = 0 ↔ bits.val < 2^63 := by omega
  norm_num at sign
  simp [SpecExt.Builtins.floatOfBits, Spec.Constants.floatValue, fun_M, E, signif, expon,
    SpecExt.Builtins.floatBias, sign]

end Itasca.Compiler

end

/-! ## Reader Float Constant Emissions -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
/-- An actual successful constant reader and compiler callback extends the
retained code prefix and the supplied source zipper together. -/
theorem reader_emit_float32 {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A)
    (C : context) (localTypes : C.LOCALS = compilerLocals before) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (types : List wasm_types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translation.valueType))
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
      Body.ReaderPost p out.core (Spec.Constants.f32 value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [.Val .F32]) ∧
      ∃ emitted, TypedLowered before after out.core.vals.val emitted (types.map Translation.valueType ++ [.F32]) ∧
        ScalarEmission C (types.map Translation.valueType) (Spec.Constants.f32 value) [emitted]
          (types.map Translation.valueType ++ [.F32])) := by
  obtain ⟨capacity, run⟩ := base_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals, p.ft.results⟩ index code.OP_F32_CONST before after (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨value, callback, _, vals, post⟩ := reader_f32_const p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity byte run
  have postConcrete : out.core.vals.val = (types ++ [Itasca.wasm_types.ValueType.F32]).map code.StackType.Val := by
    simp [vals, concrete]
  have lowered := callback_float32 ops law before out.core (types ++ [Itasca.wasm_types.ValueType.F32])
    (types.map Translation.valueType) value layout reachable postConcrete codeFits sourceFits coordinateFits
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f32_const ops before out.core value = _ at callback
  rw [callback_float32_eq] at callback
  have ordinary := compiler_op65_ordinary_result ops law before after out.core 0#u32 0#u32 (UScalar.cast .U128 value) (.Ok ()) callback
  have sources := compiler_op65_sources ops law before after out.core 0#u32 0#u32 (UScalar.cast .U128 value) callback
  have cursor := compiler_op65_cursor ops law before after out.core 0#u32 0#u32 (UScalar.cast .U128 value) callback
  refine ⟨ordinary, sources, cursor, ?_⟩
  rw [callback_float32_eq, callback, WP.spec_ok] at lowered
  have lower := lowered rfl
  simp only [List.map_append, List.map_cons, List.map_nil, Translation.valueType] at lower
  have instruction : Spec.Constants.f32 value =
      .CONST .F32 (.mk_num__1 .F32 (SpecExt.Builtins.floatOfBits 32 value.val)) := by rw [scalar_float_value_32]; rfl
  refine ⟨value, post, _, ⟨lower, SourceStack.of_map (types ++ [.F32]) postConcrete (by simp [Translation.valueType])⟩, ?_⟩
  rw [instruction]
  apply ScalarEmission.float32
  simpa only [localTypes] using layout.height

/-- An actual successful constant reader and compiler callback extends the
retained code prefix and the supplied source zipper together. -/
theorem reader_emit_float64 {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A)
    (C : context) (localTypes : C.LOCALS = compilerLocals before) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (types : List wasm_types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translation.valueType))
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
      Body.ReaderPost p out.core (Spec.Constants.f64 value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [.Val .F64]) ∧
      ∃ emitted, TypedLowered before after out.core.vals.val emitted (types.map Translation.valueType ++ [.F64]) ∧
        ScalarEmission C (types.map Translation.valueType) (Spec.Constants.f64 value) [emitted]
          (types.map Translation.valueType ++ [.F64])) := by
  obtain ⟨capacity, run⟩ := base_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals, p.ft.results⟩ index code.OP_F64_CONST before after (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨value, callback, _, vals, post⟩ := reader_f64_const p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity byte run
  have postConcrete : out.core.vals.val = (types ++ [Itasca.wasm_types.ValueType.F64]).map code.StackType.Val := by
    simp [vals, concrete]
  have lowered := callback_float64 ops law before out.core (types ++ [Itasca.wasm_types.ValueType.F64])
    (types.map Translation.valueType) value layout reachable postConcrete codeFits sourceFits coordinateFits
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f64_const ops before out.core value = _ at callback
  rw [callback_float64_eq] at callback
  have ordinary := compiler_op66_ordinary_result ops law before after out.core 0#u32 0#u32 (UScalar.cast .U128 value) (.Ok ()) callback
  have sources := compiler_op66_sources ops law before after out.core 0#u32 0#u32 (UScalar.cast .U128 value) callback
  have cursor := compiler_op66_cursor ops law before after out.core 0#u32 0#u32 (UScalar.cast .U128 value) callback
  refine ⟨ordinary, sources, cursor, ?_⟩
  rw [callback_float64_eq, callback, WP.spec_ok] at lowered
  have lower := lowered rfl
  simp only [List.map_append, List.map_cons, List.map_nil, Translation.valueType] at lower
  have instruction : Spec.Constants.f64 value =
      .CONST .F64 (.mk_num__1 .F64 (SpecExt.Builtins.floatOfBits 64 value.val)) := by rw [scalar_float_value_64]; rfl
  refine ⟨value, post, _, ⟨lower, SourceStack.of_map (types ++ [.F64]) postConcrete (by simp [Translation.valueType])⟩, ?_⟩
  rw [instruction]
  apply ScalarEmission.float64
  simpa only [localTypes] using layout.height

end Itasca.Compiler

end

end
