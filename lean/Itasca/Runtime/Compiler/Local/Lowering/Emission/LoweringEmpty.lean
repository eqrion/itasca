import Itasca.Runtime.Compiler.Local.Lowering.Emission.Emit
import Itasca.Runtime.Compiler.Local.Callbacks.Observation.Frame

/-!
Sections, each formerly its own module: Lowering, LoweringEmpty.
-/

/-! ## Lowering -/

section

/-! Checked source callbacks construct straight-line code certificates. The
current slice proves both integer constants through the actual extracted
callbacks, including bit-preserving casts, emission, source coordinates, and
post-callback operand layout. -/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Dead instructions only observe the validator state; opcode dispatch is skipped. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.dead {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (dead : before.reachable = false) :
    runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits =
      runtime.compiler.FunctionCompiler.observe ops before state := by
  unfold runtime.compiler.lower.FunctionCompiler.op
  exact if_neg (by simp only [dead, Bool.false_eq_true, not_false_eq_true])

/-- Sequencing equation for adapters proving equality of whole compiler tails. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.finish_op.eq {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (instruction : runtime.bytecode.Instr) :
    runtime.compiler.lower.FunctionCompiler.finish_op ops before state instruction = (do
      let (reply, middle) ← runtime.compiler.FunctionCompiler.emit ops before instruction
      let branch ← core.result.Result.Insts.CoreOpsTry.branch reply
      match branch with
      | .Continue _ => runtime.compiler.FunctionCompiler.observe ops middle state
      | .Break residual => do
        let error ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Unit
          (core.convert.FromSame Itasca.error.VisitError) residual
        Result.ok (error, middle)) := rfl

/-- A finished instruction either stops at emission failure or observes the
validator stack after a successful emission. These call witnesses retain the
intermediate state needed by coordinate and capacity consumers. -/
inductive FinishEffect {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (instruction : runtime.bytecode.Instr) :
    core.result.Result Unit Itasca.error.VisitError → runtime.compiler.FunctionCompiler A → Prop where
  | rejected {error after}
      (emitted : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (.Err error, after)) :
      FinishEffect ops before state instruction (.Err error) after
  | observed {middle status after}
      (emitted : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (.Ok (), middle))
      (observed : runtime.compiler.FunctionCompiler.observe ops middle state = .ok (status, after)) :
      FinishEffect ops before state instruction status after

/-- Normal returns expose the emission/observation effect without allocator laws. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.finish_op.inv {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (instruction : runtime.bytecode.Instr)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.lower.FunctionCompiler.finish_op ops before state instruction = .ok (status, after)) :
    FinishEffect ops before state instruction status after := by
  unfold runtime.compiler.lower.FunctionCompiler.finish_op at called
  obtain ⟨⟨reply, middle⟩, emitted, rest⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ called
  cases reply with
  | Err error =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
    obtain ⟨rfl, rfl⟩ := rest
    exact .rejected emitted
  | Ok unit =>
    cases unit
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    exact .observed emitted rest

theorem FinishEffect.success {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {state : Itasca.code.OpIterState}
    {instruction : runtime.bytecode.Instr}
    (effect : FinishEffect ops before state instruction (.Ok ()) after) :
    ∃ middle, runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (.Ok (), middle) ∧
      runtime.compiler.FunctionCompiler.observe ops middle state = .ok (.Ok (), after) := by
  cases effect with
  | observed emitted observed => exact ⟨_, emitted, observed⟩

/-- Bounds sufficient for emission also make its observation tail total. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.finish_op.total {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (instruction : runtime.bytecode.Instr)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state instruction ⦃ _ => True ⦄ := by
  unfold runtime.compiler.lower.FunctionCompiler.finish_op
  step with runtime.compiler.FunctionCompiler.emit.total ops law compiler instruction codeFits sourceFits coordinateFits
    as ⟨reply, middle, total⟩
  cases reply with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
  | Ok unit =>
    cases unit
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    exact WP.spec_mono (compiler_observe ops law middle state) (fun _ _ => True.intro)

/-- Numeric demand at a callback boundary. These are independent size,
coordinate, and budget bounds, not callback acceptance or code certificates. -/
structure CallbackDemand {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bound : Nat) : Prop where
  pc : compiler.function.code.length ≤ U32.max
  codeCapacity : compiler.function.code.length < Usize.max
  sourceCapacity : compiler.function.source_offsets.length < Usize.max
  codeReserve : compiler.function.code.length + 1 ≤ bound
  sourceReserve : compiler.function.source_offsets.length + 1 ≤ bound
  coordinate : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max
  instruction : compiler.budget.instructions.val < compiler.budget.limits.max_instructions.val
  operands : state.vals.length ≤ bound
  slots : compiler.function.local_slots.val + 2*state.vals.length ≤ U32.max


/-- The actual emission/observation callback tail consumes exactly one
instruction and preserves every other budget counter and marker. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.finish_op.available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (instruction : runtime.bytecode.Instr) :
    runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state instruction ⦃ out =>
      out.1 = .Ok () ∧ ∃ used, out.2.budget = {compiler.budget with instructions := used} ∧
        used.val = compiler.budget.instructions.val+1 ⦄ := by
  unfold runtime.compiler.lower.FunctionCompiler.finish_op
  step with runtime.compiler.FunctionCompiler.emit.available ops bound available compiler instruction demand.pc demand.codeCapacity
    demand.sourceCapacity demand.codeReserve demand.sourceReserve demand.coordinate demand.instruction
    as ⟨status,emitted,accepted,effect⟩
  obtain ⟨used,code,sources,shape,usedEq,appended,coordinates⟩ := effect
  rw [accepted]
  subst emitted
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  apply WP.spec_mono (compiler_observe_available_budget ops bound available
    {compiler with
      budget := {compiler.budget with instructions := used}
      function := {compiler.function with code,source_offsets := sources}} state demand.operands demand.slots)
  intro out post
  exact ⟨post.1,used,post.2,usedEq⟩


def Lowered {A : Type} (before after : runtime.compiler.FunctionCompiler A)
    (instruction : runtime.bytecode.Instr) (stack : List valtype) : Prop :=
  after.function.code.val = before.function.code.val ++ [instruction] ∧
  CompilerLayout after stack ∧ compilerLocals after = compilerLocals before ∧
  after.reachable = before.reachable ∧
  before.function.slot_count.val ≤ after.function.slot_count.val

@[step] theorem finish_op {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.wasm_types.ValueType)
    (instruction : runtime.bytecode.Instr) (before : List valtype)
    (layout : CompilerLayout compiler before)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state instruction ⦃ out =>
      out.1 = .Ok () → Lowered compiler out.2 instruction (types.map Itasca.Translate.valueType) ⦄ := by
  obtain ⟨⟨result, output⟩, called, _⟩ := WP.spec_imp_exists
    (runtime.compiler.lower.FunctionCompiler.finish_op.total ops law compiler state instruction codeFits sourceFits coordinateFits)
  rw [called, WP.spec_ok]
  intro accepted
  dsimp only at accepted ⊢
  subst result
  obtain ⟨c, emittedRun, observedRun⟩ :=
    (runtime.compiler.lower.FunctionCompiler.finish_op.inv ops compiler output state instruction (.Ok ()) called).success
  have h := compiler_emit ops law compiler instruction codeFits sourceFits coordinateFits
  rw [emittedRun, WP.spec_ok] at h
  dsimp only at h
  have emitted := h rfl
  have clayout := emitted.layout layout
  obtain ⟨budget, code, sources, hc, hcode, hsources⟩ := emitted
  have houtput := compiler_observe ops law c state
  rw [observedRun, WP.spec_ok] at houtput
  dsimp only at houtput
  obtain ⟨hoff, hh, hl, hls, hlo, hr, hpreserve, hsrc, hnext, hcap, hmono, hframes, hcontrols⟩ := houtput rfl
  have hlocals : compilerLocals output = compilerLocals c := by simp [compilerLocals, hl]
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, hcap⟩, ?_, ?_, ?_⟩
  · simpa [hpreserve, hc] using hcode
  · simpa [hls, hlocals] using clayout.localSlots
  · simpa [hlo, hlocals] using clayout.localOffsets
  · rw [hoff, concrete, observed_offsets_values, clayout.localSlots]
    simp [stackOffsets, hlocals]
  · rw [hh, concrete, observed_height_values, clayout.localSlots, hlocals]
  · simp [hl, compilerLocals, hc]
  · simpa [hc] using hr
  · simpa [hc] using hmono

set_option maxRecDepth 4096 in
@[step] theorem lower_const32 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.wasm_types.ValueType)
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
    (state : Itasca.code.OpIterState) (types : List Itasca.wasm_types.ValueType)
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
    (state : Itasca.code.OpIterState) (types : List Itasca.wasm_types.ValueType)
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
    (state : Itasca.code.OpIterState) (types : List Itasca.wasm_types.ValueType)
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

end Itasca.Runtime.Compiler

end

/-! ## LoweringEmpty -/

section

/-!
NOP and DROP update the validator-derived stack layout without emitting code.

Main declarations: `LoweredEmpty`. A direct consumer is `Compiler.Body.Source.TypedLowering`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- NOP and DROP update the validator-derived stack layout without emitting code. -/
def LoweredEmpty {A : Type} (before after : runtime.compiler.FunctionCompiler A)
    (stack : List valtype) : Prop :=
  after.function.code = before.function.code ∧
  CompilerLayout after stack ∧ compilerLocals after = compilerLocals before ∧
  after.reachable = before.reachable ∧
  before.function.slot_count.val ≤ after.function.slot_count.val

@[step] theorem compiler_observe_empty {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.wasm_types.ValueType)
    (before : List valtype) (layout : CompilerLayout compiler before)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val) :
    runtime.compiler.FunctionCompiler.observe ops compiler state ⦃ out => out.1 = .Ok () →
      LoweredEmpty compiler out.2 (types.map Itasca.Translate.valueType) ⦄ := by
  obtain ⟨out, called, info⟩ := WP.spec_imp_exists (compiler_observe ops law compiler state)
  rw [called, WP.spec_ok]
  intro accepted
  obtain ⟨_, _, locals, _, _, reachable, code, _, _, _, capacity, _, _⟩ := info accepted
  have newLayout := compiler_observe_layout ops law compiler state types concrete layout.localSlots layout.localOffsets
  rw [called, WP.spec_ok] at newLayout
  exact ⟨code, newLayout accepted, by simp [compilerLocals, locals], reachable, capacity⟩

theorem lower_empty_eq {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (drop : Bool) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (if drop then 26#u16 else 1#u16) 0#u32 0#u32 0#u128 =
      runtime.compiler.FunctionCompiler.observe ops compiler state := by
  cases drop <;> unfold runtime.compiler.lower.FunctionCompiler.op <;> split <;> rfl

end Itasca.Runtime.Compiler

end
