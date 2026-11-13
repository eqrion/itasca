import Itasca.Runtime.Compiler.Local.Source.SourceLengthsTactic
import Itasca.Runtime.Compiler.Local.Callbacks.Observation.Frame
import Itasca.Runtime.Compiler.Local.Capacity.EmissionGrowth
import Itasca.Runtime.Compiler.Local.Callbacks.CodeGrowth.PatchGrowth
import Mathlib.Tactic.FailIfNoProgress
import Mathlib.Tactic.Rename

/-!
Sections, each formerly its own module: CapacityHelpers, CapacityTactic, GrowthTactic, ControlGrowth, ControlCapacity.
-/

/-! ## CapacityHelpers -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Slot metadata unchanged by emission and patching. Only observation updates the high-water mark. -/
def capacityMetadata {A : Type} (compiler : runtime.compiler.FunctionCompiler A) :=
  (compiler.function.local_slots, compiler.function.slot_count)

theorem compiler_emit_capacity_metadata {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (status, after)) :
    capacityMetadata after = capacityMetadata before := by
  unfold runtime.compiler.FunctionCompiler.emit at accepted
  obtain ⟨⟨pc, current⟩, called, rest⟩ := bind_ok_inv _ _ _ accepted
  have effect := compiler_pc ops before
  rw [called, WP.spec_ok] at effect
  obtain ⟨_, _, budget, currentEq⟩ := effect
  change current = {before with budget} at currentEq
  subst current
  cases pc with
  | Err error =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
      obtain ⟨_, output⟩ := rest
      subst after
      rfl
  | Ok value =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    obtain ⟨⟨charged, budget1⟩, _, rest⟩ := bind_ok_inv _ _ _ rest
    cases charged with
    | Err error =>
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
        obtain ⟨_, output⟩ := rest
        subst after
        rfl
    | Ok value =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      obtain ⟨⟨pushed, budget2, code⟩, _, rest⟩ := bind_ok_inv _ _ _ rest
      cases pushed with
      | Err error =>
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
          obtain ⟨_, output⟩ := rest
          subst after
          rfl
      | Ok value =>
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
        obtain ⟨coordinate, _, rest⟩ := bind_ok_inv _ _ _ rest
        obtain ⟨⟨result, budget3, sources⟩, _, rest⟩ := bind_ok_inv _ _ _ rest
        simp only [uncurry_apply_pair, Result.ok.injEq, Prod.mk.injEq] at rest
        obtain ⟨_, output⟩ := rest
        subst after
        rfl

theorem compiler_copy_capacity_metadata {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (dst src count : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.copy ops before dst src count = .ok (status, after)) :
    capacityMetadata after = capacityMetadata before := by
  unfold runtime.compiler.FunctionCompiler.copy at accepted
  split at accepted
  · have same : before = after := (Prod.mk.inj (Result.ok.injEq.mp accepted)).2
    subst after
    rfl
  · split at accepted
    · have same : before = after := (Prod.mk.inj (Result.ok.injEq.mp accepted)).2
      subst after
      rfl
    · obtain ⟨instruction, _, emitted⟩ := bind_ok_inv _ _ _ accepted
      exact compiler_emit_capacity_metadata ops before after instruction status emitted

theorem compiler_pc_capacity_metadata {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A)
    (status : core.result.Result U32 Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.pc ops before = .ok (status, after)) :
    capacityMetadata after = capacityMetadata before := by
  have effect := compiler_pc ops before
  rw [accepted, WP.spec_ok] at effect
  obtain ⟨_, _, budget, same⟩ := effect
  simpa only [capacityMetadata] using congrArg capacityMetadata same
/-- Patching only replaces an instruction; all function and control metadata
survive every normal return, including a rejected patch site. -/
theorem compiler_patch_capacity_metadata {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (pc : Usize) (target : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.patch ops before pc target = .ok (status, after)) :
    capacityMetadata after = capacityMetadata before := by
  rcases compiler_patch_cases ops before after pc target status accepted with rfl | ⟨_, _, rfl, _⟩ <;>
    rfl


theorem compiler_pair_capacity_metadata {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (a b : U32)
    (status : core.result.Result U32 Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.pair ops before a b = .ok (status, after)) :
    capacityMetadata after = capacityMetadata before := by
  unfold runtime.compiler.FunctionCompiler.pair at accepted
  obtain ⟨result, _, rest⟩ := bind_ok_inv _ _ _ accepted
  cases result with
  | Err error =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
      obtain ⟨_, output⟩ := rest
      subst after
      rfl
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
        rfl
    | Ok value =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at rest
      obtain ⟨_, output⟩ := rest
      subst after
      rfl


theorem compiler_fixups_capacity_metadata {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (sites : alloc.vec.Vec Usize)
    (target : U32) (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (output : CompilerSnapshot A)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0
      ops before sites target index status = .ok output) :
    capacityMetadata (snapshotCompiler output) = capacityMetadata before := by
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
        rfl
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
        exact (ih _ smaller middle nextIndex result tail' rfl).trans
          (compiler_patch_capacity_metadata ops before middle site target result patched)
    · simp only [bind_ok, Result.ok.injEq] at accepted
      subst output
      rfl

theorem compiler_fixups_after_if_capacity_metadata {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (sites : alloc.vec.Vec Usize)
    (target : U32) (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (output : CompilerSnapshot A)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop1
      ops before sites target index status = .ok output) :
    capacityMetadata (snapshotCompiler output) = capacityMetadata before :=
  compiler_fixups_capacity_metadata ops before sites target index status output accepted


/-- Successful observation bounds capacity by the current validated operand
width and the previous high-water mark. No liveness or stack-layout premise is
needed; unreachable observations leave capacity unchanged. -/
theorem compiler_observe_capacity_bound {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.observe ops before state = .ok (status, after)) :
    after.function.local_slots = before.function.local_slots ∧
      (status = .Ok () → after.function.slot_count.val ≤
        max before.function.slot_count.val (observedHeight before.function.local_slots.val state.vals.val)) := by
  have frame := compiler_observe_frame ops law before state
  rw [accepted, WP.spec_ok] at frame
  dsimp only at frame
  refine ⟨by rw [frame], ?_⟩
  intro success
  have measures := compiler_observe_measures ops law before state
  rw [accepted, WP.spec_ok] at measures
  rw [(measures success).2]
  split
  · exact Nat.le_refl _
  · exact Nat.le_max_left _ _

theorem compiler_finish_op_capacity_bound {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (instruction : runtime.bytecode.Instr)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.finish_op ops before state instruction = .ok (status, after)) :
    status = .Ok () → after.function.local_slots = before.function.local_slots ∧
      after.function.slot_count.val ≤
        max before.function.slot_count.val (observedHeight before.function.local_slots.val state.vals.val) := by
  intro success
  subst status
  unfold runtime.compiler.lower.FunctionCompiler.finish_op at accepted
  obtain ⟨⟨result, middle⟩, emitted, rest⟩ := bind_ok_inv _ _ _ accepted
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok value =>
    cases value
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    have preserve := compiler_emit_capacity_metadata ops before middle instruction (.Ok ()) emitted
    have ⟨locals, bound⟩ := compiler_observe_capacity_bound ops law middle after state (.Ok ()) rest
    have fields : middle.function.local_slots = before.function.local_slots ∧
        middle.function.slot_count = before.function.slot_count := by
      simpa only [capacityMetadata, Prod.mk.injEq] using preserve
    exact ⟨locals.trans fields.1, by simpa only [fields.1, fields.2] using bound rfl⟩
/-- One accepted source callback may only raise capacity to the observed
validated stack height. The local prefix stays fixed. -/
def CapacityStep {A : Type} (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) : Prop :=
  after.function.local_slots = before.function.local_slots ∧
    after.function.slot_count.val ≤ max before.function.slot_count.val
      (observedHeight before.function.local_slots.val state.vals.val)
end Itasca.Runtime.Compiler

end

/-! ## CapacityTactic -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
open Lean Meta Elab Tactic in
elab "capacity_effect " h:ident " using " ops:term ", " law:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  let some functionName := lhs.getAppFn.constName? | throwError "not a named helper"
  let tac ← match functionName with
    | ``runtime.compiler.FunctionCompiler.observe =>
      `(tactic| have effect := compiler_observe_capacity_bound $ops $law _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.emit =>
      `(tactic| have effect := compiler_emit_capacity_metadata $ops _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.copy =>
      `(tactic| have effect := compiler_copy_capacity_metadata $ops _ _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.pair =>
      `(tactic| have effect := compiler_pair_capacity_metadata $ops _ _ _ _ _ $h)
    | ``runtime.compiler.lower.FunctionCompiler.finish_op =>
      `(tactic| have effect := compiler_finish_op_capacity_bound $ops $law _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.pc => do
      let theoremName := mkIdent `Itasca.Runtime.Compiler.compiler_pc_capacity_metadata
      `(tactic| have effect := $theoremName $ops _ _ _ $h)
    | ``runtime.compiler.control.FunctionCompiler.patch => do
      let theoremName := mkIdent `Itasca.Runtime.Compiler.compiler_patch_capacity_metadata
      `(tactic| have effect := $theoremName $ops _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0 => do
      let theoremName := mkIdent `Itasca.Runtime.Compiler.compiler_fixups_capacity_metadata
      `(tactic| have effect := $theoremName $ops _ _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop1 => do
      let theoremName := mkIdent `Itasca.Runtime.Compiler.compiler_fixups_after_if_capacity_metadata
      `(tactic| have effect := $theoremName $ops _ _ _ _ _ _ $h)
    | _ => throwError "not a compiler helper"
  evalTactic tac


macro "capacity_close" : tactic => `(tactic|
  (first | rfl | (simp_all [snapshotCompiler, source_unit_eq, CapacityStep, capacityMetadata]; try omega)))
macro "capacity_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (sources_terminal $h; capacity_close)
  | (fail_if_no_progress dsimp only at $h:ident)
  | solve | (capacity_effect $h using $ops, $law; capacity_close)
  | solve | (sources_terminal $h; have output := (Prod.mk.inj (Result.ok.injEq.mp $h)).2; cases output; capacity_close)
  | (fail_if_no_progress simp only [Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok] at $h:ident)
  | (sources_nonterminal $h
     obtain ⟨value, called, rest⟩ := bind_ok_inv _ _ _ $h
     clear $h
     rename' rest => $h
     first
     | (guard_hyp value : Prod _ _; rcases value with ⟨firstValue, secondValue⟩)
     | skip
     try capacity_effect called using $ops, $law
     first
     | (guard_hyp firstValue : core.result.Result _ _; cases firstValue)
     | (guard_hyp value : core.result.Result _ _; cases value)
     | skip
     try simp only [uncurry_apply_pair] at $h:ident)
  | (fail_if_no_progress simp only [Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok] at $h:ident)
  | sources_split $h)


end Itasca.Runtime.Compiler

end

/-! ## GrowthTactic -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

open Lean Meta Elab Tactic in
elab "growth_effect " h:ident " using " ops:term ", " law:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  let some functionName := lhs.getAppFn.constName? | throwError "not a named helper"
  let tac ← match functionName with
    | ``runtime.compiler.FunctionCompiler.observe =>
      `(tactic| have effect := compiler_observe_code_result $ops $law _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.emit =>
      `(tactic| have effect := compiler_emit_growth $ops $law _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.copy =>
      `(tactic| have effect := compiler_copy_growth $ops $law _ _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.pair =>
      `(tactic| have effect := compiler_pair_code_result $ops _ _ _ _ _ $h)
    | ``runtime.compiler.lower.FunctionCompiler.finish_op =>
      `(tactic| have effect := compiler_finish_op_growth $ops $law _ _ _ _ _ $h)
    | ``runtime.compiler.simd.FunctionCompiler.simd_op => do
      let theoremName := mkIdent `Itasca.Runtime.Compiler.compiler_simd_growth
      `(tactic| have effect := $theoremName $ops $law _ _ _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.pc => do
      let theoremName := mkIdent `Itasca.Runtime.Compiler.compiler_pc_code_result
      `(tactic| have effect := $theoremName $ops _ _ _ $h)
    | ``runtime.compiler.control.FunctionCompiler.patch => do
      let theoremName := mkIdent `Itasca.Runtime.Compiler.compiler_patch_code_length
      `(tactic| have effect := $theoremName $ops _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0 => do
      let theoremName := mkIdent `Itasca.Runtime.Compiler.compiler_fixups_code_length
      `(tactic| have effect := $theoremName $ops _ _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop1 => do
      let theoremName := mkIdent `Itasca.Runtime.Compiler.compiler_fixups_after_if_code_length
      `(tactic| have effect := $theoremName $ops _ _ _ _ _ _ $h)
    | _ => throwError "not a compiler helper"
  evalTactic tac


macro "growth_close" : tactic => `(tactic|
  (try simp_all only [snapshotCompiler, Prod.mk.injEq]
   try omega))

macro "growth_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (growth_effect $h using $ops, $law; growth_close)
  | solve | (simp only [Result.ok.injEq, Prod.mk.injEq] at $h:ident; obtain ⟨_, output⟩ := $h; cases output; growth_close)
  | (obtain ⟨value, called, rest⟩ := bind_ok_inv _ _ _ $h
     clear $h
     rename' rest => $h
     first
     | (guard_hyp value : Prod _ _; rcases value with ⟨firstValue, secondValue⟩)
     | skip
     try growth_effect called using $ops, $law
     try simp only [uncurry_apply_pair] at $h:ident)
  | (fail_if_no_progress simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok] at $h:ident)
  | split at $h:ident)

end Itasca.Runtime.Compiler

end

/-! ## ControlGrowth -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

theorem compiler_branch_growth {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (status, after)) :
    after.function.code.val.length ≤ before.function.code.val.length + (if conditional then 3 else 2) := by
  cases conditional <;>
    simp only [runtime.compiler.control.FunctionCompiler.branch, Bool.false_eq_true, ite_false, ite_true] at accepted ⊢ <;>
    repeat' growth_step accepted using ops, law

end Itasca.Runtime.Compiler

end

/-! ## ControlCapacity -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
theorem compiler_enter_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind)
    (blockType : Itasca.signature.BlockType)
    (accepted : runtime.compiler.control.FunctionCompiler.enter ops before state kind blockType = .ok (.Ok (), after)) :
    CapacityStep before after state := by
  unfold runtime.compiler.control.FunctionCompiler.enter at accepted
  repeat' capacity_step accepted using ops, law
  all_goals try (casesm* core.result.Result Never _ <;> try casesm* Never)
  all_goals repeat' capacity_step accepted using ops, law
theorem compiler_branch_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (.Ok (), after)) :
    capacityMetadata after = capacityMetadata before := by
  cases conditional <;>
    simp only [runtime.compiler.control.FunctionCompiler.branch, Bool.false_eq_true, ite_false, ite_true] at accepted <;>
    repeat' capacity_step accepted using ops, law
  all_goals try (casesm* core.result.Result Never _ <;> try casesm* Never)
  all_goals repeat' capacity_step accepted using ops, law
theorem compiler_end_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind)
    (blockType : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end
      ops before state kind blockType = .ok (.Ok (), after)) :
    CapacityStep before after state := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end at accepted
  repeat' capacity_step accepted using ops, law
  all_goals try (casesm* core.result.Result Never _ <;> try casesm* Never)
  all_goals repeat' capacity_step accepted using ops, law

theorem compiler_else_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (blockType : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else
      ops before state blockType = .ok (.Ok (), after)) :
    CapacityStep before after state := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else at accepted
  simp only [core.option.Option.take] at accepted
  repeat' capacity_step accepted using ops, law
  all_goals try (casesm* core.result.Result Never _ <;> try casesm* Never)
  all_goals repeat' capacity_step accepted using ops, law


end Itasca.Runtime.Compiler

end
