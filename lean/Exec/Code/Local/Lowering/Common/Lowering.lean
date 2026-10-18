import Exec.Code.Local.Lowering.Common.Emit
import Exec.Code.Local.Callbacks.Common.Observe

/-! Checked source callbacks construct straight-line code certificates. The
current slice proves both integer constants through the actual extracted
callbacks, including bit-preserving casts, emission, source coordinates, and
post-callback operand layout. -/

namespace Exec.Code
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

theorem Lowered.linear_code {A : Type} {compiler output : runtime.compiler.FunctionCompiler A}
    {instruction stack before source} (lowered : Lowered compiler output instruction stack)
    (emission : LinearEmission (compilerLocals compiler) before source [instruction] stack) :
    LinearCodeRel (compilerLocals compiler) before [source] output.function.code.val
      compiler.function.code.val.length (compiler.function.code.val.length + 1) stack := by
  refine ⟨compiler.function.code.val, [instruction], [], ?_, rfl, rfl, ?_⟩
  · simpa using lowered.1
  · simpa using LinearRel.cons emission (LinearRel.nil stack)

@[step] theorem callback_const32_certificate {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
    (before : List valtype) (value : I32)
    (layout : CompilerLayout compiler before) (reachable : compiler.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = before ++ [.I32])
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_const ops compiler state value ⦃ out =>
      out.1 = .Ok () →
        LinearCodeRel (compilerLocals compiler) before
          [.CONST .I32 (.mk_num__0 .I32 (.mk_uN (IScalar.hcast .U32 value).val))]
          out.2.function.code.val compiler.function.code.val.length
          (compiler.function.code.val.length + 1) (before ++ [.I32]) ∧
        CompilerLayout out.2 (before ++ [.I32]) ⦄ := by
  step with callback_const32 ops law compiler state types before value layout reachable concrete
    codeFits sourceFits coordinateFits as ⟨out, hout, success⟩
  have lowered := hout success
  rw [typed] at lowered
  exact ⟨lowered.linear_code (LinearEmission.const32 before compiler.height
    (IScalar.hcast .U32 value) layout.height), lowered.2.1⟩

@[step] theorem callback_const64_certificate {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
    (before : List valtype) (value : I64)
    (layout : CompilerLayout compiler before) (reachable : compiler.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = before ++ [.I64])
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_const ops compiler state value ⦃ out =>
      out.1 = .Ok () →
        LinearCodeRel (compilerLocals compiler) before
          [.CONST .I64 (.mk_num__0 .I64 (.mk_uN (IScalar.hcast .U64 value).val))]
          out.2.function.code.val compiler.function.code.val.length
          (compiler.function.code.val.length + 1) (before ++ [.I64]) ∧
        CompilerLayout out.2 (before ++ [.I64]) ⦄ := by
  step with callback_const64 ops law compiler state types before value layout reachable concrete
    codeFits sourceFits coordinateFits as ⟨out, hout, success⟩
  have lowered := hout success
  rw [typed] at lowered
  exact ⟨lowered.linear_code (LinearEmission.const64 before compiler.height
    (IScalar.hcast .U64 value) layout.height), lowered.2.1⟩

/-- Append a checked lowering step to the retained straight-line prefix. -/
theorem Lowered.extend_prefix {A : Type} {compiler output : runtime.compiler.FunctionCompiler A}
    {instruction before after locals initial source next}
    (lowered : Lowered compiler output instruction after)
    (inv : LinearCompileInv compiler locals initial source before)
    (emission : LinearEmission locals before next [instruction] after) :
    LinearCompileInv output locals initial (source ++ [next]) after := by
  refine ⟨lowered.2.2.1.trans inv.localsEq, lowered.2.1, ?_⟩
  rw [lowered.1]
  simpa using inv.code.append (LinearRel.cons emission (LinearRel.nil after))

/-- A successful push fits its complete destination inside the output frame. -/
theorem Lowered.new_top_fits {A : Type}
    {compiler output : runtime.compiler.FunctionCompiler A} {instruction before ty}
    (lowered : Lowered compiler output instruction (before ++ [ty]))
    (layout : CompilerLayout compiler before) (reachable : compiler.reachable = true) :
    compiler.height.val + width ty ≤ output.function.slot_count.val := by
  have capacity := lowered.2.1.capacity (lowered.2.2.2.1.trans reachable)
  rw [lowered.2.1.height, lowered.2.2.1, slots_append] at capacity
  simpa [layout.height, slots, Nat.add_assoc] using capacity

theorem Lowered.preserve_slot_bound {A : Type}
    {compiler output : runtime.compiler.FunctionCompiler A} {instruction stack index}
    (lowered : Lowered compiler output instruction stack)
    (inside : index < compiler.function.slot_count.val) :
    index < output.function.slot_count.val := by
  have := lowered.2.2.2.2
  omega

end Exec.Code
