import Itasca.Runtime.Compiler.Local.Lowering.Control.BranchEffects
import Itasca.Runtime.Compiler.Local.Lowering.Control.BranchContracts
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EndContracts
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseContracts
import Itasca.Runtime.Compiler.Local.Lowering.Emission.Copy
import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty
import Itasca.Runtime.Compiler.Local.Lowering.Emission.Pair
import Itasca.Runtime.Compiler.Local.Lowering.Emission.Emit
import Itasca.Runtime.Compiler.Local.Source.SourceLengthsTactic
import Itasca.Runtime.Compiler.Local.Callbacks.Observation.Frame
import Itasca.Runtime.Compiler.Local.Capacity.EmissionGrowth
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Mathlib.Tactic.FailIfNoProgress
import Mathlib.Tactic.Rename

/-!
Sections, each formerly its own module: CapacityHelpers, CapacityTactic, GrowthTactic, ControlGrowth, ControlCapacity.
-/

/-! ## CapacityHelpers -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- Slot metadata unchanged by emission and patching. Only observation updates the high-water mark. -/
def capacityMetadata {A : Type} (compiler : runtime.compiler.FunctionCompiler A) :=
  (compiler.function.local_slots, compiler.function.slot_count)

theorem compiler_emit_capacity_metadata {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (status, after)) :
    capacityMetadata after = capacityMetadata before := by
  have frame := (runtime.compiler.FunctionCompiler.emit.inv ops before after instruction status accepted).1
  change after = _ at frame
  rw [frame]
  rfl

theorem compiler_copy_capacity_metadata {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (dst src count : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.copy ops before dst src count = .ok (status, after)) :
    capacityMetadata after = capacityMetadata before := by
  have frame := (runtime.compiler.FunctionCompiler.copy.inv ops before after dst src count status accepted).frame
  change after = _ at frame
  rw [frame]
  rfl

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
  have frame := (runtime.compiler.FunctionCompiler.pair.inv ops before after a b status accepted).1
  change after = _ at frame
  rw [frame]
  rfl


theorem compiler_fixups_capacity_metadata {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (sites : alloc.vec.Vec Usize)
    (target : U32) (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (output : CompilerSnapshot A)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0
      ops before sites target index status = .ok output) :
    capacityMetadata (snapshotCompiler output) = capacityMetadata before := by
  obtain ⟨code, same⟩ := (compiler_fixups_effect ops before sites target index status output accepted).1
  rw [same]; rfl

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
  obtain ⟨middle, emitted, rest⟩ :=
    (runtime.compiler.lower.FunctionCompiler.finish_op.inv ops before after state instruction (.Ok ()) accepted).success
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



end Itasca.Runtime.Compiler

end

/-! ## ControlGrowth -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts


end Itasca.Runtime.Compiler

end

/-! ## ControlCapacity -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
theorem compiler_enter_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind)
    (blockType : Itasca.signature.BlockType)
    (accepted : runtime.compiler.control.FunctionCompiler.enter ops before state kind blockType = .ok (.Ok (), after)) :
    CapacityStep before after state := by
  obtain ⟨prior, ctrl, signature, height, startPc, condition, source, middle,
    controls, selected, heightEq, sourceEq, operand, publish, observed⟩ :=
      (runtime.compiler.control.FunctionCompiler.enter.inv ops before after state kind blockType (.Ok ()) accepted).2.2 rfl
  have publication := publish law
  have observedFrame := compiler_observe_frame ops law middle state
  rw [observed, WP.spec_ok] at observedFrame
  change after = _ at observedFrame
  have measures := compiler_observe_measures ops law middle state
  rw [observed, WP.spec_ok] at measures
  have frame := publication.frame
  change middle = _ at frame
  unfold CapacityStep
  rw [observedFrame]
  refine ⟨?_, ?_⟩
  · rw [frame]
  · have bounded := (measures rfl).2
    rw [bounded]
    split
    · rw [frame]
    · rw [frame]
      exact Nat.le_max_left _ _


theorem compiler_branch_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (.Ok (), after)) :
    capacityMetadata after = capacityMetadata before := by
  have frame := (runtime.compiler.control.FunctionCompiler.branch.inv ops before after depth skip conditional (.Ok ()) accepted).frame
  rw [frame]
  rfl

theorem compiler_end_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind)
    (blockType : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end
      ops before state kind blockType = .ok (.Ok (), after)) :
    CapacityStep before after state := by
  have effect := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end.inv ops before after state kind blockType (.Ok ()) accepted
  obtain ⟨middle, observed, slots, locals⟩ := effect.observation_slots
  have post := compiler_observe_capacity_bound ops law middle after state (.Ok ()) observed
  exact ⟨post.1.trans locals, by simpa only [slots, locals] using post.2 rfl⟩

theorem compiler_else_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (blockType : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else
      ops before state blockType = .ok (.Ok (), after)) :
    CapacityStep before after state := by
  have effect := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else.inv ops before after state blockType (.Ok ()) accepted
  obtain ⟨middle, observed, slots, locals⟩ := effect.observation_slots
  have post := compiler_observe_capacity_bound ops law middle after state (.Ok ()) observed
  exact ⟨post.1.trans locals, by simpa only [slots, locals] using post.2 rfl⟩

end Itasca.Runtime.Compiler

end
