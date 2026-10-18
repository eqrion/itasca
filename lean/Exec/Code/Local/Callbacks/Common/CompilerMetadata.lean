import Exec.Code.Local.Callbacks.Common.ObserveFrame
import Exec.Code.Local.Callbacks.Common.ObserveMeasures
import Exec.Code.Local.Callbacks.Common.Finish
import Exec.Code.Local.Callbacks.Common.Fixups
namespace Exec.Code
open Aeneas Aeneas.Std
open Itasca.ResultFacts

/-- Source and local-layout metadata fixed after the function-start callback.
Instruction emission and control-flow patching may change work buffers only. -/
def compilerMetadata {A : Type} (compiler : runtime.compiler.FunctionCompiler A) :=
  (compiler.signatures, compiler.func_param_slots, compiler.batch_start,
    compiler.function.type_index, compiler.function.locals, compiler.function.param_slots,
    compiler.function.local_slots, compiler.function.body_start, compiler.function.body_end,
    compiler.local_offsets)

structure CompilerStable {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop where
  metadata : compilerMetadata after = compilerMetadata before
  capacity : before.function.slot_count.val ≤ after.function.slot_count.val

theorem CompilerStable.refl {A : Type} (compiler : runtime.compiler.FunctionCompiler A) :
    CompilerStable compiler compiler := ⟨rfl, Nat.le_refl _⟩

theorem CompilerStable.trans {A : Type} {before middle after : runtime.compiler.FunctionCompiler A}
    (first : CompilerStable before middle) (second : CompilerStable middle after) :
    CompilerStable before after := ⟨second.metadata.trans first.metadata, first.capacity.trans second.capacity⟩

theorem CompilerStable.fields {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (stable : CompilerStable before after) :
    after.signatures = before.signatures ∧ after.func_param_slots = before.func_param_slots ∧
    after.batch_start = before.batch_start ∧ after.function.type_index = before.function.type_index ∧
    after.function.locals = before.function.locals ∧ after.function.param_slots = before.function.param_slots ∧
    after.function.local_slots = before.function.local_slots ∧ after.function.body_start = before.function.body_start ∧
    after.function.body_end = before.function.body_end ∧ after.local_offsets = before.local_offsets := by
  simpa only [compilerMetadata, Prod.mk.injEq] using stable.metadata

theorem Emitted.stable {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {instruction} (emitted : Emitted before after instruction) : CompilerStable before after := by
  obtain ⟨budget, code, sources, rfl, _, _⟩ := emitted
  exact ⟨rfl, Nat.le_refl _⟩

theorem OnlyCode.stable {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (changed : OnlyCode before after) : CompilerStable before after := by
  obtain ⟨code, rfl⟩ := changed
  exact ⟨rfl, Nat.le_refl _⟩

/-- A successful observation preserves fixed metadata and only increases the
slot capacity. Its allocation decisions and current validator operands vary freely. -/
theorem compiler_observe_stable {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (accepted : runtime.compiler.FunctionCompiler.observe ops before state = .ok (.Ok (), after)) :
    CompilerStable before after := by
  have frame := compiler_observe_frame ops law before state
  rw [accepted, WP.spec_ok] at frame
  have measures := compiler_observe_measures ops law before state
  rw [accepted, WP.spec_ok] at measures
  constructor
  · simpa only [ObserveFrame, compilerMetadata] using congrArg compilerMetadata frame
  · rw [(measures rfl).2]
    split
    · exact Nat.le_max_left _ _
    · exact Nat.le_refl _

/-- Successful emission preserves fixed metadata without requiring any spare
capacity or coordinate premise: a success equation already witnesses those checks. -/
theorem compiler_emit_stable {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr)
    (accepted : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (.Ok (), after)) :
    CompilerStable before after := by
  unfold runtime.compiler.FunctionCompiler.emit at accepted
  obtain ⟨⟨pc, current⟩, called, rest⟩ := bind_ok_inv _ _ _ accepted
  have effect := compiler_pc ops before
  rw [called, WP.spec_ok] at effect
  obtain ⟨_, _, budget, currentEq⟩ := effect
  change current = {before with budget} at currentEq
  subst current
  cases pc with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok value =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    obtain ⟨⟨charged, budget1⟩, _, rest⟩ := bind_ok_inv _ _ _ rest
    cases charged with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok value =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      obtain ⟨⟨pushed, budget2, code⟩, _, rest⟩ := bind_ok_inv _ _ _ rest
      cases pushed with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
      | Ok value =>
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
        obtain ⟨coordinate, _, rest⟩ := bind_ok_inv _ _ _ rest
        obtain ⟨⟨result, budget3, sources⟩, _, rest⟩ := bind_ok_inv _ _ _ rest
        simp only [uncurry_apply_pair, Result.ok.injEq, Prod.mk.injEq] at rest
        obtain ⟨_, output⟩ := rest
        subst after
        exact ⟨rfl, Nat.le_refl _⟩

theorem compiler_copy_stable {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (dst src count : U32)
    (accepted : runtime.compiler.FunctionCompiler.copy ops before dst src count = .ok (.Ok (), after)) :
    CompilerStable before after := by
  unfold runtime.compiler.FunctionCompiler.copy at accepted
  split at accepted
  · have same : before = after := by simpa using accepted
    subst after
    exact .refl _
  · split at accepted
    · have same : before = after := by simpa using accepted
      subst after
      exact .refl _
    · obtain ⟨instruction, _, emitted⟩ := bind_ok_inv _ _ _ accepted
      exact compiler_emit_stable ops before after instruction emitted

theorem compiler_pair_stable {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (a b index : U32)
    (accepted : runtime.compiler.FunctionCompiler.pair ops before a b = .ok (.Ok index, after)) :
    CompilerStable before after := by
  unfold runtime.compiler.FunctionCompiler.pair at accepted
  obtain ⟨result, _, rest⟩ := bind_ok_inv _ _ _ accepted
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok value =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    obtain ⟨⟨result, budget, pairs⟩, _, rest⟩ := bind_ok_inv _ _ _ rest
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok value =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at rest
      obtain ⟨_, output⟩ := rest
      subst after
      exact ⟨rfl, Nat.le_refl _⟩

theorem compiler_finish_op_stable {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (instruction : runtime.bytecode.Instr)
    (accepted : runtime.compiler.lower.FunctionCompiler.finish_op ops before state instruction = .ok (.Ok (), after)) :
    CompilerStable before after := by
  unfold runtime.compiler.lower.FunctionCompiler.finish_op at accepted
  obtain ⟨⟨result, middle⟩, emitted, rest⟩ := bind_ok_inv _ _ _ accepted
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok value =>
    cases value
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    exact (compiler_emit_stable ops before middle instruction emitted).trans
      (compiler_observe_stable ops law middle after state rest)
end Exec.Code
