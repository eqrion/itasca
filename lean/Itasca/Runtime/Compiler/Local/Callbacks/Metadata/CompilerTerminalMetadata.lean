import Itasca.Runtime.Compiler.Local.Lowering.Emission.Emit
import Itasca.Runtime.Compiler.Local.Callbacks.Observation.Frame
import Itasca.Runtime.Compiler.Local.Callbacks.Function.EnterDead
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupAlgebra
import Mathlib.Tactic.FailIfNoProgress
import Mathlib.Tactic.Rename

/-!
Sections, each formerly its own module: CompilerMetadata, CompilerOrdinaryMetadata, CompilerOrdinaryResults, CompilerPatchMetadata, CompilerFixupMetadata, CompilerMetadataTactic, CompilerEnterMetadata, CompilerCloseMetadata, CompilerDeadMetadata, CompilerLiteralMetadata, CompilerTerminalMetadata.
-/

/-! ## CompilerMetadata -/

section

/-!
Source and local-layout metadata fixed after the function-start callback. Instruction emission and control-flow patching may change work buffers only.

Main declarations: `compilerMetadata` and `CompilerStable`. A direct consumer is `Compiler.Local.Callbacks.Metadata.CompilerOrdinaryMetadata`.
-/

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## CompilerOrdinaryMetadata -/

section

/-!
Ordinary instructions leave the frame stack and its control-map entries fixed.

Main declarations: `compilerOrdinaryMetadata` and `CompilerOrdinaryStable`. A direct consumer is `Compiler.Local.Callbacks.Metadata.CompilerOrdinaryResults`.
-/

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## CompilerOrdinaryResults -/

section

/-!
Ordinary postconditions of observe, emit, copy and finish operations.

Main declarations: `compiler_observe_ordinary_post` and `compiler_finish_op_ordinary_result`. A direct consumer is `Compiler.Local.Callbacks.Metadata.CompilerDeadMetadata`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

theorem compiler_observe_ordinary_post {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) :
    runtime.compiler.FunctionCompiler.observe ops compiler state ⦃ out =>
      CompilerOrdinaryStable compiler out.2 ⦄ := by
  apply WP.spec_mono (compiler_observe_inv ops law compiler state)
  intro out post
  refine ⟨?_, post.2⟩
  simpa only [ObserveFrame, compilerOrdinaryMetadata, compilerMetadata] using
    congrArg compilerOrdinaryMetadata post.1

theorem compiler_observe_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.observe ops before state = .ok (status, after)) :
    CompilerOrdinaryStable before after := by
  have result := compiler_observe_ordinary_post ops law before state
  simpa only [accepted, WP.spec_ok] using result

theorem compiler_emit_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (status, after)) :
    CompilerOrdinaryStable before after := by
  have frame := (runtime.compiler.FunctionCompiler.emit.inv ops before after instruction status accepted).1
  change after = _ at frame
  rw [frame]
  exact ⟨rfl, Nat.le_refl _⟩

theorem compiler_copy_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (dst src count : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.copy ops before dst src count = .ok (status, after)) :
    CompilerOrdinaryStable before after := by
  unfold runtime.compiler.FunctionCompiler.copy at accepted
  split at accepted
  · have same : before = after := (Prod.mk.inj (Result.ok.injEq.mp accepted)).2
    subst after
    exact .refl _
  · split at accepted
    · have same : before = after := (Prod.mk.inj (Result.ok.injEq.mp accepted)).2
      subst after
      exact .refl _
    · obtain ⟨instruction, _, emitted⟩ := bind_ok_inv _ _ _ accepted
      exact compiler_emit_ordinary_result ops before after instruction status emitted

theorem compiler_pair_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (a b : U32)
    (status : core.result.Result U32 Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.pair ops before a b = .ok (status, after)) :
    CompilerOrdinaryStable before after := by
  unfold runtime.compiler.FunctionCompiler.pair at accepted
  obtain ⟨result, _, rest⟩ := bind_ok_inv _ _ _ accepted
  cases result with
  | Err error =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
      obtain ⟨_, output⟩ := rest
      subst after
      exact ⟨rfl, Nat.le_refl _⟩
  | Ok value =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    obtain ⟨⟨result, budget, pairs⟩, _, rest⟩ := bind_ok_inv _ _ _ rest
    cases result with
    | Err error =>
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
        obtain ⟨_, output⟩ := rest
        subst after
        exact ⟨rfl, Nat.le_refl _⟩
    | Ok value =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at rest
      obtain ⟨_, output⟩ := rest
      subst after
      exact ⟨rfl, Nat.le_refl _⟩

theorem compiler_finish_op_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (instruction : runtime.bytecode.Instr)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.finish_op ops before state instruction = .ok (status, after)) :
    CompilerOrdinaryStable before after := by
  unfold runtime.compiler.lower.FunctionCompiler.finish_op at accepted
  obtain ⟨⟨result, middle⟩, emitted, rest⟩ := bind_ok_inv _ _ _ accepted
  cases result with
  | Err error =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
      obtain ⟨_, output⟩ := rest
      subst after
      exact compiler_emit_ordinary_result ops before middle instruction (.Err error) emitted
  | Ok value =>
    cases value
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    exact (compiler_emit_ordinary_result ops before middle instruction (.Ok ()) emitted).trans
      (compiler_observe_ordinary_result ops law middle after state status rest)
end Itasca.Runtime.Compiler

end

/-! ## CompilerPatchMetadata -/

section

/-!
Patching only replaces an instruction; all function and control metadata survive every normal return, including a rejected patch site.

Main declarations: `compiler_patch_ordinary_result` and `compiler_pc_ordinary_result`. A direct consumer is `Compiler.Local.Callbacks.Control.CompilerBranchMetadata`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Patching only replaces an instruction; all function and control metadata
survive every normal return, including a rejected patch site. -/
theorem compiler_patch_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (pc : Usize) (target : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.patch ops before pc target = .ok (status, after)) :
    CompilerOrdinaryStable before after := by
  rcases compiler_patch_cases ops before after pc target status accepted with rfl | ⟨_, _, rfl, _⟩ <;>
    exact ⟨rfl, Nat.le_refl _⟩

/-- PC calculation may reject its range but only updates the budget. -/
theorem compiler_pc_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A)
    (status : core.result.Result U32 Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.pc ops before = .ok (status, after)) :
    CompilerOrdinaryStable before after := by
  have result := compiler_pc ops before
  rw [accepted, WP.spec_ok] at result
  obtain ⟨_, _, budget, same⟩ := result
  change after = {before with budget} at same
  subst after
  exact ⟨rfl, Nat.le_refl _⟩
end Itasca.Runtime.Compiler

end

/-! ## CompilerFixupMetadata -/

section

/-!
Compiler snapshots and metadata effects of branch fixups.

Main declarations: `CompilerSnapshot` and `snapshotCompiler`. A direct consumer is `Compiler.Local.Callbacks.CodeGrowth.PatchGrowth`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

abbrev CompilerSnapshot (A : Type) :=
  Slice runtime.compiler.Signature × Slice U32 × runtime.compiler.Budget A × Usize ×
  runtime.bytecode.CompiledFunction × alloc.vec.Vec runtime.compiler.Frame × Bool × Usize ×
  alloc.vec.Vec U32 × U32 × alloc.vec.Vec U32 × alloc.vec.Vec U32 ×
  core.result.Result Unit Itasca.error.VisitError

def snapshotCompiler {A : Type} (output : CompilerSnapshot A) : runtime.compiler.FunctionCompiler A :=
  let (signatures, functionSlots, budget, batchStart, function, frames, reachable,
    nextSource, operands, height, offsets, depths, _) := output
  ⟨signatures, functionSlots, budget, batchStart, function, frames, reachable,
    nextSource, operands, height, offsets, depths⟩

theorem compiler_fixups_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (sites : alloc.vec.Vec Usize)
    (target : U32) (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (output : CompilerSnapshot A)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0
      ops before sites target index status = .ok output) :
    CompilerOrdinaryStable before (snapshotCompiler output) := by
  generalize measure : Usize.max - index.val = n
  induction n using Nat.strong_induction_on generalizing before index status with
  | h n ih =>
    unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0 at accepted
    rw [loop] at accepted
    simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0.body,
      bind_ok] at accepted
    split at accepted
    · cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq] at accepted
        subst output
        exact .refl _
      | Ok unit =>
        cases unit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte, Std.bind_assoc] at accepted
        obtain ⟨site, _, rest⟩ := bind_ok_inv _ _ _ accepted
        obtain ⟨⟨result, middle⟩, patched, tail⟩ := bind_ok_inv _ _ _ rest
        simp only [uncurry_apply_pair, Std.bind_assoc, bind_ok] at tail
        obtain ⟨nextIndex, increment, tail⟩ := bind_ok_inv _ _ _ tail
        have arithmetic := UScalar.add_equiv index 1#usize
        rw [increment] at arithmetic
        have progress : nextIndex.val = index.val + 1 := by simpa using arithmetic.2.1
        have nextMax := nextIndex.hmax
        have smaller : Usize.max - nextIndex.val < n := by scalar_tac
        have tail' : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0
            ops middle sites target nextIndex result = .ok output := by
          simpa only [uncurry_apply_pair, bind_ok,
            runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0,
            runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0.body,
            core.result.Result.is_ok] using tail
        exact (compiler_patch_ordinary_result ops before middle site target result patched).trans
          (ih _ smaller middle nextIndex result tail' rfl)
    · simp only [bind_ok, Result.ok.injEq] at accepted
      subst output
      exact .refl _

theorem compiler_fixups_after_if_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (sites : alloc.vec.Vec Usize)
    (target : U32) (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (output : CompilerSnapshot A)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop1
      ops before sites target index status = .ok output) :
    CompilerOrdinaryStable before (snapshotCompiler output) :=
  compiler_fixups_ordinary_result ops before sites target index status output accepted
end Itasca.Runtime.Compiler

end

/-! ## CompilerMetadataTactic -/

section

/-!
Proof automation for compiler metadata effects.

Main declarations: `metadata_effect` and `metadata_close`. A direct consumer is `Compiler.Local.Callbacks.Calls.CompilerCallbackMetadata`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

open Lean Meta Elab Tactic in
elab "metadata_effect " h:ident " using " ops:term ", " law:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  let some functionName := lhs.getAppFn.constName? | throwError "not a named helper"
  let tac ← match functionName with
    | ``runtime.compiler.FunctionCompiler.observe =>
      `(tactic| have effect := compiler_observe_ordinary_result $ops $law _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.emit =>
      `(tactic| have effect := compiler_emit_ordinary_result $ops _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.copy =>
      `(tactic| have effect := compiler_copy_ordinary_result $ops _ _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.pair =>
      `(tactic| have effect := compiler_pair_ordinary_result $ops _ _ _ _ _ $h)
    | ``runtime.compiler.lower.FunctionCompiler.finish_op =>
      `(tactic| have effect := compiler_finish_op_ordinary_result $ops $law _ _ _ _ _ $h)
    | ``runtime.compiler.simd.FunctionCompiler.simd_op => do
      let theoremName := mkIdent `Itasca.Runtime.Compiler.compiler_simd_ordinary_result
      `(tactic| have effect := $theoremName $ops $law _ _ _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.pc => do
      let theoremName := mkIdent `Itasca.Runtime.Compiler.compiler_pc_ordinary_result
      `(tactic| have effect := $theoremName $ops _ _ _ $h)
    | ``runtime.compiler.control.FunctionCompiler.patch => do
      let theoremName := mkIdent `Itasca.Runtime.Compiler.compiler_patch_ordinary_result
      `(tactic| have effect := $theoremName $ops _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0 => do
      let theoremName := mkIdent `Itasca.Runtime.Compiler.compiler_fixups_ordinary_result
      `(tactic| have effect := $theoremName $ops _ _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop1 => do
      let theoremName := mkIdent `Itasca.Runtime.Compiler.compiler_fixups_after_if_ordinary_result
      `(tactic| have effect := $theoremName $ops _ _ _ _ _ _ $h)
    | _ => throwError "not a compiler helper"
  evalTactic tac
  evalTactic (← `(tactic| have metadataEq := effect.metadata))
  evalTactic (← `(tactic| have capacity := effect.capacity))

macro "metadata_close" : tactic => `(tactic|
  (constructor
   · first | rfl | simp_all only [compilerOrdinaryMetadata, compilerMetadata, snapshotCompiler, Prod.mk.injEq]
   · try simp_all only [compilerOrdinaryMetadata, compilerMetadata, snapshotCompiler, Prod.mk.injEq]
     try omega))

macro "metadata_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (metadata_effect $h using $ops, $law; metadata_close)
  | solve | (simp only [Result.ok.injEq, Prod.mk.injEq] at $h:ident; obtain ⟨_, output⟩ := $h; cases output; metadata_close)
  | (obtain ⟨value, called, rest⟩ := bind_ok_inv _ _ _ $h
     clear $h
     rename' rest => $h
     first
     | (guard_hyp value : Prod _ _; rcases value with ⟨firstValue, secondValue⟩)
     | skip
     try metadata_effect called using $ops, $law
     try simp only [uncurry_apply_pair] at $h:ident)
  | (fail_if_no_progress simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok] at $h:ident)
  | split at $h:ident)

end Itasca.Runtime.Compiler

end

/-! ## CompilerEnterMetadata -/

section

/-!
Compiler metadata retained when entering a scope.

Main declarations: `compiler_enter_stable_result`. A direct consumer is `Compiler.Local.Callbacks.Calls.CompilerCallbackMetadata`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem compiler_enter_stable_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind)
    (blockType : Itasca.signature.BlockType)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.enter ops before state kind blockType = .ok (status, after)) :
    CompilerStable before after := by
  obtain ⟨frame, monotone, _⟩ := runtime.compiler.control.FunctionCompiler.enter.inv ops before after state kind blockType status accepted
  refine ⟨?_, monotone law⟩
  change after = _ at frame
  rw [frame]
  rfl


end Itasca.Runtime.Compiler

end

/-! ## CompilerCloseMetadata -/

section

/-!
Compiler metadata retained by end and else callbacks.

Main declarations: `compiler_end_stable_result` and `compiler_else_stable_result`. A direct consumer is `Compiler.Module.CompileSlice`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem compiler_end_stable_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind)
    (blockType : Itasca.signature.BlockType)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end
      ops before state kind blockType = .ok (status, after)) :
    CompilerStable before after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end at accepted
  repeat' metadata_step accepted using ops, law

theorem compiler_else_stable_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (blockType : Itasca.signature.BlockType)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else
      ops before state blockType = .ok (status, after)) :
    CompilerStable before after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else at accepted
  simp only [core.option.Option.take] at accepted
  repeat' metadata_step accepted using ops, law
end Itasca.Runtime.Compiler

end

/-! ## CompilerDeadMetadata -/

section

/-!
Ordinary opcodes in an unreachable suffix only observe the validator. In particular, they emit no code and preserve the structured-control frames.

Main declarations: `compiler_dead_op_frame` and `compiler_dead_op_fields`. A direct consumer is `Compiler.Module.CompileSlice`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Ordinary opcodes in an unreachable suffix only observe the validator.
In particular, they emit no code and preserve the structured-control frames. -/
theorem compiler_dead_op_frame {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (dead : compiler.reachable = false) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state opcode a b bits ⦃ out =>
      ObserveFrame compiler out.2 ⦄ := by
  rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (dead)]
  exact compiler_observe_frame ops law compiler state

theorem compiler_dead_op_fields {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (dead : compiler.reachable = false) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state opcode a b bits ⦃ out =>
      out.2.function.code = compiler.function.code ∧ out.2.frames = compiler.frames ∧
      out.2.function.locals = compiler.function.locals ∧ out.2.reachable = false ⦄ := by
  apply WP.spec_mono (compiler_dead_op_frame ops law compiler state opcode a b bits dead)
  intro out frame
  rw [frame]
  exact ⟨rfl, rfl, rfl, dead⟩
end Itasca.Runtime.Compiler

end

/-! ## CompilerLiteralMetadata -/

section

/-!
Ordinary compiler effects of literal and basic scalar callbacks.

Main declarations: `compiler_op65_ordinary_result` and `compiler_drop_ordinary_result`. A direct consumer is `Compiler.Module.CompileSlice`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem compiler_op65_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 65#u16 a b bits = .ok (status, after)) :
    CompilerOrdinaryStable before after := by
  by_cases reach : before.reachable = true
  · have run : runtime.compiler.lower.FunctionCompiler.op ops before state 65#u16 a b bits = (do
        let i ← lift (UScalar.cast .U32 bits)
        runtime.compiler.lower.FunctionCompiler.finish_op ops before
          state (runtime.bytecode.Instr.Const32 before.height i)) := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_pos reach]
      rfl
    rw [run] at accepted
    repeat' metadata_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_ordinary_result ops law before after state status accepted

theorem compiler_op66_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 66#u16 a b bits = .ok (status, after)) :
    CompilerOrdinaryStable before after := by
  by_cases reach : before.reachable = true
  · have run : runtime.compiler.lower.FunctionCompiler.op ops before state 66#u16 a b bits = (do
        let i ← lift (UScalar.cast .U64 bits)
        runtime.compiler.lower.FunctionCompiler.finish_op ops before
          state (runtime.bytecode.Instr.Const64 before.height i)) := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_pos reach]
      rfl
    rw [run] at accepted
    repeat' metadata_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_ordinary_result ops law before after state status accepted

theorem compiler_op32_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 32#u16 a b bits = .ok (status, after)) :
    CompilerOrdinaryStable before after := by
  by_cases reach : before.reachable = true
  · have run : runtime.compiler.lower.FunctionCompiler.op ops before state 32#u16 a b bits = (do
        let i ← lift (UScalar.cast .Usize a)
        let src ←
          alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.U32)
            before.local_offsets i
        let i1 ← lift (UScalar.cast .Usize a)
        let vt ←
          alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
            _root_.Itasca.wasm_types.ValueType) before.function.locals i1
        let n ← runtime.value.width vt
        let (r, self1) ←
          runtime.compiler.FunctionCompiler.copy ops before
            before.height src n
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          runtime.compiler.FunctionCompiler.observe ops self1 state
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r1 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
              residual
          Result.ok (r1, self1)) := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_pos reach]
      rfl
    rw [run] at accepted
    repeat' metadata_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_ordinary_result ops law before after state status accepted

theorem compiler_op33_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 33#u16 a b bits = .ok (status, after)) :
    CompilerOrdinaryStable before after := by
  by_cases reach : before.reachable = true
  · have run : runtime.compiler.lower.FunctionCompiler.op ops before state 33#u16 a b bits = (do
        let i ← lift (UScalar.cast .Usize a)
        let dst ←
          alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.U32)
            before.local_offsets i
        let r ←
          runtime.compiler.FunctionCompiler.operand ops before
            1#usize
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | core.ops.control_flow.ControlFlow.Continue val =>
          let i1 ← lift (UScalar.cast .Usize a)
          let vt ←
            alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
              _root_.Itasca.wasm_types.ValueType) before.function.locals i1
          let n ← runtime.value.width vt
          let (r1, self1) ←
            runtime.compiler.FunctionCompiler.copy ops before dst val
              n
          let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
          match cf1 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            runtime.compiler.FunctionCompiler.observe ops self1 state
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r2 ←
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
                residual
            Result.ok (r2, self1)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r1 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
              residual
          Result.ok (r1, before)) := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_pos reach]
      rfl
    rw [run] at accepted
    repeat' metadata_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_ordinary_result ops law before after state status accepted

theorem compiler_op34_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 34#u16 a b bits = .ok (status, after)) :
    CompilerOrdinaryStable before after := by
  by_cases reach : before.reachable = true
  · have run : runtime.compiler.lower.FunctionCompiler.op ops before state 34#u16 a b bits = (do
        let i ← lift (UScalar.cast .Usize a)
        let dst ←
          alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.U32)
            before.local_offsets i
        let r ←
          runtime.compiler.FunctionCompiler.operand ops before
            1#usize
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | core.ops.control_flow.ControlFlow.Continue val =>
          let i1 ← lift (UScalar.cast .Usize a)
          let vt ←
            alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
              _root_.Itasca.wasm_types.ValueType) before.function.locals i1
          let n ← runtime.value.width vt
          let (r1, self1) ←
            runtime.compiler.FunctionCompiler.copy ops before dst val
              n
          let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
          match cf1 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            runtime.compiler.FunctionCompiler.observe ops self1 state
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r2 ←
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
                residual
            Result.ok (r2, self1)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r1 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
              residual
          Result.ok (r1, before)) := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_pos reach]
      rfl
    rw [run] at accepted
    repeat' metadata_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_ordinary_result ops law before after state status accepted

theorem compiler_op16_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 16#u16 a b bits = .ok (status, after)) :
    CompilerOrdinaryStable before after := by
  by_cases reach : before.reachable = true
  · have run : runtime.compiler.lower.FunctionCompiler.op ops before state 16#u16 a b bits = (do
        let i ← lift (UScalar.cast .Usize a)
        let slots ← Slice.index_usize before.func_param_slots i
        let o ← lift (U32.checked_sub before.height slots)
        let r ←
          core.option.Option.ok_or o _root_.Itasca.error.VisitError.OutOfMemory
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | core.ops.control_flow.ControlFlow.Continue val =>
          runtime.compiler.lower.FunctionCompiler.finish_op ops
            before state (runtime.bytecode.Instr.Call a val)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r1 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
              residual
          Result.ok (r1, before)) := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_pos reach]
      rfl
    rw [run] at accepted
    repeat' metadata_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_ordinary_result ops law before after state status accepted

theorem compiler_op1_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 1#u16 a b bits = .ok (status, after)) :
    CompilerOrdinaryStable before after := by
  by_cases reach : before.reachable = true
  · have run : runtime.compiler.lower.FunctionCompiler.op ops before state 1#u16 a b bits = (do
        runtime.compiler.FunctionCompiler.observe ops before state) := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_pos reach]
      rfl
    rw [run] at accepted
    repeat' metadata_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_ordinary_result ops law before after state status accepted

theorem compiler_op26_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 26#u16 a b bits = .ok (status, after)) :
    CompilerOrdinaryStable before after := by
  by_cases reach : before.reachable = true
  · have run : runtime.compiler.lower.FunctionCompiler.op ops before state 26#u16 a b bits = (do
        runtime.compiler.FunctionCompiler.observe ops before state) := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_pos reach]
      rfl
    rw [run] at accepted
    repeat' metadata_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_ordinary_result ops law before after state status accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_i32_const_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : I32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_const
      ops before state value = .ok (status, after)) : CompilerOrdinaryStable before after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_const at accepted
  simp only [lift, bind_ok] at accepted
  exact compiler_op65_ordinary_result ops law before after state _ _ _ status accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_i64_const_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : I64)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_const
      ops before state value = .ok (status, after)) : CompilerOrdinaryStable before after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_const at accepted
  simp only [lift, bind_ok] at accepted
  exact compiler_op66_ordinary_result ops law before after state _ _ _ status accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_local_get_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_get
      ops before state value = .ok (status, after)) : CompilerOrdinaryStable before after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_get at accepted
  exact compiler_op32_ordinary_result ops law before after state _ _ _ status accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_local_set_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_set
      ops before state value = .ok (status, after)) : CompilerOrdinaryStable before after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_set at accepted
  exact compiler_op33_ordinary_result ops law before after state _ _ _ status accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_local_tee_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_tee
      ops before state value = .ok (status, after)) : CompilerOrdinaryStable before after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_tee at accepted
  exact compiler_op34_ordinary_result ops law before after state _ _ _ status accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_call_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_call
      ops before state value = .ok (status, after)) : CompilerOrdinaryStable before after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_call at accepted
  exact compiler_op16_ordinary_result ops law before after state _ _ _ status accepted

theorem compiler_nop_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_nop
      ops before state = .ok (status, after)) : CompilerOrdinaryStable before after := by
  exact compiler_op1_ordinary_result ops law before after state _ _ _ status accepted

theorem compiler_drop_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (dropped : Itasca.code.StackType) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_drop
      ops before state dropped = .ok (status, after)) : CompilerOrdinaryStable before after := by
  exact compiler_op26_ordinary_result ops law before after state _ _ _ status accepted

end Itasca.Runtime.Compiler

end

/-! ## CompilerTerminalMetadata -/

section

/-!
Ordinary compiler effects of unreachable and return callbacks.

Main declarations: `compiler_unreachable_ordinary_result` and `compiler_return_ordinary_result`. A direct consumer is `Compiler.Module.CompileSlice`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem compiler_unreachable_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable ops before state = .ok (status, after)) :
    CompilerOrdinaryStable before after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable at accepted
  repeat' metadata_step accepted using ops, law

theorem compiler_return_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return ops before state = .ok (status, after)) :
    CompilerOrdinaryStable before after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return at accepted
  repeat' metadata_step accepted using ops, law
end Itasca.Runtime.Compiler

end
