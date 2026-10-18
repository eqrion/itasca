import Exec.Code.Local.Callbacks.Common.CompilerMetadata
namespace Exec.Code
open Aeneas Aeneas.Std
open Itasca.ResultFacts

/-- Ordinary instructions leave the frame stack and its control-map entries fixed. -/
def compilerOrdinaryMetadata {A : Type} (compiler : runtime.compiler.FunctionCompiler A) :=
  (compilerMetadata compiler, compiler.frames, compiler.function.controls)

structure CompilerOrdinaryStable {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop where
  metadata : compilerOrdinaryMetadata after = compilerOrdinaryMetadata before
  capacity : before.function.slot_count.val ≤ after.function.slot_count.val

theorem CompilerOrdinaryStable.refl {A : Type} (compiler : runtime.compiler.FunctionCompiler A) :
    CompilerOrdinaryStable compiler compiler := ⟨rfl, Nat.le_refl _⟩

theorem CompilerOrdinaryStable.trans {A : Type} {before middle after : runtime.compiler.FunctionCompiler A}
    (first : CompilerOrdinaryStable before middle) (second : CompilerOrdinaryStable middle after) :
    CompilerOrdinaryStable before after := ⟨second.metadata.trans first.metadata, first.capacity.trans second.capacity⟩

theorem CompilerOrdinaryStable.stable {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (stable : CompilerOrdinaryStable before after) : CompilerStable before after :=
  ⟨congrArg Prod.fst stable.metadata, stable.capacity⟩

theorem CompilerOrdinaryStable.frames {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (stable : CompilerOrdinaryStable before after) : after.frames = before.frames :=
  congrArg (fun metadata => metadata.2.1) stable.metadata

theorem CompilerOrdinaryStable.controls {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (stable : CompilerOrdinaryStable before after) : after.function.controls = before.function.controls :=
  congrArg (fun metadata => metadata.2.2) stable.metadata

theorem Emitted.ordinary_stable {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {instruction} (emitted : Emitted before after instruction) : CompilerOrdinaryStable before after := by
  obtain ⟨budget, code, sources, rfl, _, _⟩ := emitted
  exact ⟨rfl, Nat.le_refl _⟩

theorem OnlyCode.ordinary_stable {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (changed : OnlyCode before after) : CompilerOrdinaryStable before after := by
  obtain ⟨code, rfl⟩ := changed
  exact ⟨rfl, Nat.le_refl _⟩

/-- A successful observation preserves fixed metadata and only increases the
slot capacity. Its allocation decisions and current validator operands vary freely. -/
theorem compiler_observe_ordinary_stable {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (accepted : runtime.compiler.FunctionCompiler.observe ops before state = .ok (.Ok (), after)) :
    CompilerOrdinaryStable before after := by
  have frame := compiler_observe_frame ops law before state
  rw [accepted, WP.spec_ok] at frame
  have measures := compiler_observe_measures ops law before state
  rw [accepted, WP.spec_ok] at measures
  constructor
  · simpa only [ObserveFrame, compilerOrdinaryMetadata, compilerMetadata] using congrArg compilerOrdinaryMetadata frame
  · rw [(measures rfl).2]
    split
    · exact Nat.le_max_left _ _
    · exact Nat.le_refl _

/-- Successful emission preserves fixed metadata without requiring any spare
capacity or coordinate premise: a success equation already witnesses those checks. -/
theorem compiler_emit_ordinary_stable {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr)
    (accepted : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (.Ok (), after)) :
    CompilerOrdinaryStable before after := by
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

theorem compiler_copy_ordinary_stable {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (dst src count : U32)
    (accepted : runtime.compiler.FunctionCompiler.copy ops before dst src count = .ok (.Ok (), after)) :
    CompilerOrdinaryStable before after := by
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
      exact compiler_emit_ordinary_stable ops before after instruction emitted

theorem compiler_pair_ordinary_stable {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (a b index : U32)
    (accepted : runtime.compiler.FunctionCompiler.pair ops before a b = .ok (.Ok index, after)) :
    CompilerOrdinaryStable before after := by
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

theorem compiler_finish_op_ordinary_stable {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (instruction : runtime.bytecode.Instr)
    (accepted : runtime.compiler.lower.FunctionCompiler.finish_op ops before state instruction = .ok (.Ok (), after)) :
    CompilerOrdinaryStable before after := by
  unfold runtime.compiler.lower.FunctionCompiler.finish_op at accepted
  obtain ⟨⟨result, middle⟩, emitted, rest⟩ := bind_ok_inv _ _ _ accepted
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok value =>
    cases value
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    exact (compiler_emit_ordinary_stable ops before middle instruction emitted).trans
      (compiler_observe_ordinary_stable ops law middle after state rest)
end Exec.Code
