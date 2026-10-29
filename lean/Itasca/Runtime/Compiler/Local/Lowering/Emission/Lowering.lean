import Itasca.Runtime.Compiler.Local.Lowering.Emission.Emit
import Itasca.Runtime.Compiler.Local.Callbacks.Observation.Observe

/-! Checked source callbacks construct straight-line code certificates. The
current slice proves both integer constants through the actual extracted
callbacks, including bit-preserving casts, emission, source coordinates, and
post-callback operand layout. -/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

def Lowered {A : Type} (before after : runtime.compiler.FunctionCompiler A)
    (instruction : runtime.bytecode.Instr) (stack : List valtype) : Prop :=
  after.function.code.val = before.function.code.val ++ [instruction] ∧
  CompilerLayout after stack ∧ compilerLocals after = compilerLocals before ∧
  after.reachable = before.reachable ∧
  before.function.slot_count.val ≤ after.function.slot_count.val

@[step] theorem finish_op {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
    (instruction : runtime.bytecode.Instr) (before : List valtype)
    (layout : CompilerLayout compiler before)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state instruction ⦃ out =>
      out.1 = .Ok () → Lowered compiler out.2 instruction (types.map Itasca.Translate.valueType) ⦄ := by
  unfold runtime.compiler.lower.FunctionCompiler.finish_op
  step with compiler_emit ops law compiler instruction codeFits sourceFits coordinateFits as ⟨r, c, h⟩
  cases r with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok value =>
    cases value
    have emitted := h rfl
    have clayout := emitted.layout layout
    obtain ⟨budget, code, sources, hc, hcode, hsources⟩ := emitted
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with compiler_observe ops law c state as ⟨out, houtput, success⟩
    rcases out with ⟨result, output⟩
    dsimp only at houtput success
    obtain ⟨hoff, hh, hl, hls, hlo, hr, hpreserve, hsrc, hnext, hcap, hmono, hframes, hcontrols⟩ := houtput success
    have hlocals : compilerLocals output = compilerLocals c := by simp [compilerLocals, hl]
    refine ⟨?_, ⟨?_, ?_, ?_, ?_, hcap⟩, ?_, ?_, ?_⟩
    · simpa [hpreserve, hc] using hcode
    · simpa [hls, hlocals] using clayout.localSlots
    · simpa [hlo, hlocals] using clayout.localOffsets
    · rw [hoff, concrete, observedOffsets_values, clayout.localSlots]
      simp [stackOffsets, hlocals]
    · rw [hh, concrete, observedHeight_values, clayout.localSlots, hlocals]
    · simp [hl, compilerLocals, hc]
    · simpa [hc] using hr
    · simpa [hc] using hmono

set_option maxRecDepth 4096 in
@[step] theorem lower_const32 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
    (before : List valtype) (bits : U128)
    (layout : CompilerLayout compiler before) (reachable : compiler.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 65#u16 0#u32 0#u32 bits ⦃ out =>
      out.1 = .Ok () → Lowered compiler out.2
        (.Const32 compiler.height (UScalar.cast .U32 bits)) (types.map Itasca.Translate.valueType) ⦄ := by
  have run : runtime.compiler.lower.FunctionCompiler.op ops compiler state 65#u16 0#u32 0#u32 bits =
      (do
        let word ← lift (UScalar.cast .U32 bits)
        runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state (.Const32 compiler.height word)) := by
    unfold runtime.compiler.lower.FunctionCompiler.op
    rw [if_pos reachable]
    rfl
  rw [run]
  step
  subst_vars
  exact finish_op ops law compiler state types _ before layout concrete codeFits sourceFits coordinateFits

set_option maxRecDepth 4096 in
@[step] theorem lower_const64 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
    (before : List valtype) (bits : U128)
    (layout : CompilerLayout compiler before) (reachable : compiler.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 66#u16 0#u32 0#u32 bits ⦃ out =>
      out.1 = .Ok () → Lowered compiler out.2
        (.Const64 compiler.height (UScalar.cast .U64 bits)) (types.map Itasca.Translate.valueType) ⦄ := by
  have run : runtime.compiler.lower.FunctionCompiler.op ops compiler state 66#u16 0#u32 0#u32 bits =
      (do
        let word ← lift (UScalar.cast .U64 bits)
        runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state (.Const64 compiler.height word)) := by
    unfold runtime.compiler.lower.FunctionCompiler.op
    rw [if_pos reachable]
    rfl
  rw [run]
  step
  subst_vars
  exact finish_op ops law compiler state types _ before layout concrete codeFits sourceFits coordinateFits

@[step] theorem callback_const32 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
    (before : List valtype) (value : I32)
    (layout : CompilerLayout compiler before) (reachable : compiler.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_const ops compiler state value ⦃ out =>
      out.1 = .Ok () → Lowered compiler out.2
        (.Const32 compiler.height (IScalar.hcast .U32 value)) (types.map Itasca.Translate.valueType) ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_const
  simp only [lift, bind_ok]
  have bits : UScalar.cast .U32 (UScalar.cast .U128 (IScalar.hcast .U32 value)) =
      IScalar.hcast .U32 value := by
    apply UScalar.eq_of_val_eq
    simp only [UScalar.cast_val_eq]
    scalar_tac
  simpa only [bits] using lower_const32 ops law compiler state types before
    (UScalar.cast .U128 (IScalar.hcast .U32 value)) layout reachable concrete
    codeFits sourceFits coordinateFits

@[step] theorem callback_const64 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
    (before : List valtype) (value : I64)
    (layout : CompilerLayout compiler before) (reachable : compiler.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_const ops compiler state value ⦃ out =>
      out.1 = .Ok () → Lowered compiler out.2
        (.Const64 compiler.height (IScalar.hcast .U64 value)) (types.map Itasca.Translate.valueType) ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_const
  simp only [lift, bind_ok]
  have bits : UScalar.cast .U64 (UScalar.cast .U128 (IScalar.hcast .U64 value)) =
      IScalar.hcast .U64 value := by
    apply UScalar.eq_of_val_eq
    simp only [UScalar.cast_val_eq]
    scalar_tac
  simpa only [bits] using lower_const64 ops law compiler state types before
    (UScalar.cast .U128 (IScalar.hcast .U64 value)) layout reachable concrete
    codeFits sourceFits coordinateFits

end Itasca.Runtime.Code
