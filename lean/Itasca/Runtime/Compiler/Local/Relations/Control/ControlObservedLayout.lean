import Itasca.Runtime.Compiler.Local.Lowering.Emission.Emit
import Itasca.Runtime.Compiler.Local.Source.SourceLengthsTactic
import Itasca.Runtime.Compiler.Local.Callbacks.Observation.Frame
import Itasca.Runtime.Compiler.Local.Relations.Layout.ValueRegions
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Local.Relations.Control.ResolvedBranchPrefix
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EnterIf

/-!
Sections, each formerly its own module: BranchReachable, ControlMapCounts, BranchSuccessControls, ControlEntrySuccess, ControlObservation, ControlObservedLayout.
-/

/-! ## BranchReachable -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
theorem compiler_emit_reachable {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (status, after)) :
    after.reachable = before.reachable := by
  have frame := (runtime.compiler.FunctionCompiler.emit.inv ops before after instruction status accepted).1
  change after = _ at frame
  rw [frame]

theorem compiler_copy_reachable {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (dst src count : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.copy ops before dst src count = .ok (status, after)) :
    after.reachable = before.reachable := by
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
      exact compiler_emit_reachable ops before after instruction status emitted

theorem compiler_pc_reachable {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A)
    (status : core.result.Result U32 Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.pc ops before = .ok (status, after)) :
    after.reachable = before.reachable := by
  have effect := compiler_pc ops before
  rw [accepted, WP.spec_ok] at effect
  obtain ⟨_, _, budget, same⟩ := effect
  exact congrArg (fun c => c.reachable) same
/-- Patching only replaces an instruction; all function and control metadata
survive every normal return, including a rejected patch site. -/
theorem compiler_patch_reachable {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (pc : Usize) (target : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.patch ops before pc target = .ok (status, after)) :
    after.reachable = before.reachable := by
  rcases compiler_patch_cases ops before after pc target status accepted with rfl | ⟨_, _, rfl, _⟩ <;>
    rfl



theorem compiler_observe_reachable {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.observe ops before state = .ok (status, after)) :
    after.reachable = before.reachable := by
  have frame := compiler_observe_frame ops law before state
  rw [accepted, WP.spec_ok] at frame
  change ObserveFrame before after at frame
  rw [frame]
open Lean Meta Elab Tactic in
elab "reachable_effect " h:ident " using " ops:term ", " law:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  let some functionName := lhs.getAppFn.constName? | throwError "not a named helper"
  let tac ← match functionName with
    | ``runtime.compiler.FunctionCompiler.observe =>
      `(tactic| have effect := compiler_observe_reachable $ops $law _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.emit =>
      `(tactic| have effect := compiler_emit_reachable $ops _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.copy =>
      `(tactic| have effect := compiler_copy_reachable $ops _ _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.pc => do
      let theoremName := mkIdent `Itasca.Runtime.Compiler.compiler_pc_reachable
      `(tactic| have effect := $theoremName $ops _ _ _ $h)
    | ``runtime.compiler.control.FunctionCompiler.patch => do
      let theoremName := mkIdent `Itasca.Runtime.Compiler.compiler_patch_reachable
      `(tactic| have effect := $theoremName $ops _ _ _ _ _ $h)
    | _ => throwError "not a compiler helper"
  evalTactic tac


macro "reachable_close" : tactic => `(tactic|
  (first | rfl | (simp_all [snapshotCompiler, source_unit_eq]; try omega)))
macro "reachable_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (sources_terminal $h; reachable_close)
  | (fail_if_no_progress dsimp only at $h:ident)
  | solve | (reachable_effect $h using $ops, $law; reachable_close)
  | solve | (sources_terminal $h; have output := (Prod.mk.inj (Result.ok.injEq.mp $h)).2; cases output; reachable_close)
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
     try reachable_effect called using $ops, $law
     first
     | (guard_hyp firstValue : core.result.Result _ _; cases firstValue)
     | (guard_hyp value : core.result.Result _ _; cases value)
     | skip
     try simp only [uncurry_apply_pair] at $h:ident)
  | (fail_if_no_progress simp only [Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok] at $h:ident)
  | sources_split $h)




theorem compiler_branch_reachable_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (status, after)) :
    after.reachable = before.reachable := by
  cases conditional <;>
    simp only [runtime.compiler.control.FunctionCompiler.branch, Bool.false_eq_true, ite_false, ite_true] at accepted <;>
    repeat' reachable_step accepted using ops, law

theorem callback_branch_if_reachable_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (view : Itasca.signature.ResultType)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
      ops before state depth view = .ok (status, after)) :
    after.reachable = before.reachable := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if at accepted
  split at accepted
  · obtain ⟨⟨result, middle⟩, called, rest⟩ := bind_ok_inv _ _ _ accepted
    have kept := compiler_branch_reachable_result ops law before middle depth 1#u32 true result called
    cases result with
    | Err error =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
      obtain ⟨_, rfl⟩ := rest
      exact kept
    | Ok value =>
      cases value
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      exact (compiler_observe_reachable ops law middle after state status rest).trans kept
  · exact compiler_observe_reachable ops law before after state status accepted

theorem callback_branch_if_layout {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (view : Itasca.signature.ResultType)
    (known : ConcreteStack state.vals.val) (locals : LocalLayout after)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
      ops before state depth view = .ok (.Ok (), after)) :
    CompilerLayout after (Itasca.Sequence.stackTypes state.vals.val) := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if at accepted
  split at accepted
  · obtain ⟨⟨result, middle⟩, called, rest⟩ := bind_ok_inv _ _ _ accepted
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok value =>
      cases value
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      exact compiler_observe_layout_success ops law middle after state known locals rest
  · exact compiler_observe_layout_success ops law before after state known locals accepted
end Itasca.Runtime.Compiler

end

/-! ## ControlMapCounts -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

private theorem vector_restore {T : Type} (vector : alloc.vec.Vec T) (index : Usize)
    (value : T) (restore : T → alloc.vec.Vec T)
    (accepted : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice T) vector index = .ok (value, restore)) :
    restore = fun value => vector.set index value := by
  rw [alloc.vec.Vec.index_mut_slice_index] at accepted
  unfold alloc.vec.Vec.index_mut_usize at accepted
  obtain ⟨selected, _, accepted⟩ := bind_ok_inv _ _ _ accepted
  exact (Prod.mk.inj (Result.ok.injEq.mp accepted)).2.symm

macro "maps_effect " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | have restoreEq := vector_restore _ _ _ _ $h
  | metadata_effect $h using $ops, $law)
macro "maps_close" : tactic => `(tactic|
  first | rfl | simp_all only [compilerOrdinaryMetadata, compilerMetadata, snapshotCompiler,
    Prod.mk.injEq, alloc.vec.Vec.set_val_eq, List.length_set])
macro "maps_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (maps_effect $h using $ops, $law; maps_close)
  | solve | (sources_terminal $h; simp only [Result.ok.injEq, Prod.mk.injEq] at $h:ident; obtain ⟨_, output⟩ := $h; cases output; maps_close)
  | (fail_if_no_progress dsimp only at $h:ident)
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
     try maps_effect called using $ops, $law
     try simp only [uncurry_apply_pair] at $h:ident)
  | sources_split $h)

theorem compiler_end_map_count {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (status, after)) :
    after.function.controls.val.length = before.function.controls.val.length := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end at accepted
  repeat' maps_step accepted using ops, law

theorem compiler_else_map_count {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops before state bt = .ok (status, after)) :
    after.function.controls.val.length = before.function.controls.val.length := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else at accepted
  simp only [core.option.Option.take] at accepted
  repeat' maps_step accepted using ops, law
end Itasca.Runtime.Compiler

end

/-! ## BranchSuccessControls -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
/-- Branch emission only changes instructions, frame fixups and operand metadata;
it never changes the structural control map, including on a normal rejection. -/
theorem compiler_branch_controls_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (status, after)) :
    after.function.controls = before.function.controls := by
  cases conditional <;>
    simp only [runtime.compiler.control.FunctionCompiler.branch, Bool.false_eq_true, ite_false, ite_true] at accepted <;>
    repeat' maps_step accepted using ops, law

theorem callback_branch_controls_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (ty : Itasca.signature.ResultType)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br ops before state depth ty = .ok (status, after)) :
    after.function.controls = before.function.controls := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br at accepted
  split at accepted
  · obtain ⟨⟨result, middle⟩, branchCall, rest⟩ := bind_ok_inv _ _ _ accepted
    have kept := compiler_branch_controls_result ops law before middle depth 0#u32 false result branchCall
    cases result with
    | Err error =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
      obtain ⟨_, rfl⟩ := rest
      exact kept
    | Ok value =>
      cases value
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      have observed := compiler_observe_ordinary_result ops law _ after state status rest
      exact observed.controls.trans kept
  · exact (compiler_observe_ordinary_result ops law before after state status accepted).controls

theorem callback_branch_if_controls_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (ty : Itasca.signature.ResultType)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if ops before state depth ty = .ok (status, after)) :
    after.function.controls = before.function.controls := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if at accepted
  split at accepted
  · obtain ⟨⟨result, middle⟩, branchCall, rest⟩ := bind_ok_inv _ _ _ accepted
    have kept := compiler_branch_controls_result ops law before middle depth 1#u32 true result branchCall
    cases result with
    | Err error =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
      obtain ⟨_, rfl⟩ := rest
      exact kept
    | Ok value =>
      cases value
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      have observed := compiler_observe_ordinary_result ops law middle after state status rest
      exact observed.controls.trans kept
  · exact (compiler_observe_ordinary_result ops law before after state status accepted).controls
end Itasca.Runtime.Compiler

end

/-! ## ControlEntrySuccess -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Successful entry computes its exact slot and byte coordinates before any
allocation. These bounds follow from the actual checked model's normal return,
so dormant entries need no speculative source-stack size premise. -/
theorem control_entry_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (success : runtime.compiler.control.FunctionCompiler.enter ops before state kind bt = .ok (.Ok (), after)) :
    before.function.local_slots.val + stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max ∧
      before.function.body_start.val + before.next_source.val ≤ Usize.max := by
  obtain ⟨priorFound, ctrlFound, signature, height, startPc, condition, source, middle,
    controlsFound, selected, heightEq, sourceEq, operand, publish, observed⟩ :=
      (runtime.compiler.control.FunctionCompiler.enter.inv ops before after state kind bt (.Ok ()) success).2.2 rfl
  have controlEq : ctrlFound = ctrl := by
    have last := congrArg List.getLast? (controlsFound.symm.trans controls)
    simpa only [List.getLast?_append, List.getLast?_singleton, Option.or, Option.some.injEq] using last
  subst ctrlFound
  have exactHeight := control_stack_height_success state.vals.deref ctrl.value_stack_base
    before.function.local_slots height (by simpa only [alloc.vec.Vec.deref, Slice.from_val] using valuesFit) heightEq
  constructor
  · have bounded := height.hmax
    simp only [alloc.vec.Vec.deref, Slice.from_val] at exactHeight
    scalar_tac
  · have bounded := source.hmax
    scalar_tac


end Itasca.Runtime.Compiler

end

/-! ## ControlObservation -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open Lean Meta Elab Tactic in
elab "observation_finish " h:ident : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  unless lhs.getAppFn.constName? = some ``runtime.compiler.FunctionCompiler.observe do
    throwError "not the final observation"
  evalTactic (← `(tactic| exact ⟨_, $h⟩))

macro "observation_step " h:ident : tactic => `(tactic|
  first
  | solve | observation_finish $h
  | solve | (sources_terminal $h; simp at $h:ident)
  | (fail_if_no_progress dsimp only at $h:ident)
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
     first
     | (guard_hyp firstValue : core.result.Result _ _; cases firstValue)
     | (guard_hyp value : core.result.Result _ _; cases value)
     | skip
     try simp only [uncurry_apply_pair] at $h:ident)
  | sources_split $h)

/-- Successful control entry ends by observing the actual post-reader stack. -/
theorem compiler_enter_observation {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (accepted : runtime.compiler.control.FunctionCompiler.enter ops before state kind bt = .ok (.Ok (), after)) :
    ∃ middle, runtime.compiler.FunctionCompiler.observe ops middle state = .ok (.Ok (), after) := by
  obtain ⟨prior, ctrl, signature, height, startPc, condition, source, middle,
    controls, selected, heightEq, sourceEq, operand, publish, observed⟩ :=
      (runtime.compiler.control.FunctionCompiler.enter.inv ops before after state kind bt (.Ok ()) accepted).2.2 rfl
  exact ⟨middle, observed⟩


theorem compiler_end_observation {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (), after)) :
    ∃ middle, runtime.compiler.FunctionCompiler.observe ops middle state = .ok (.Ok (), after) := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end at accepted
  repeat' observation_step accepted
  all_goals try (casesm* core.result.Result Never _ <;> try casesm* Never)
  all_goals repeat' observation_step accepted
  all_goals simp_all

theorem compiler_else_observation {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (bt : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops before state bt = .ok (.Ok (), after)) :
    ∃ middle, runtime.compiler.FunctionCompiler.observe ops middle state = .ok (.Ok (), after) := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else at accepted
  simp only [core.option.Option.take] at accepted
  repeat' observation_step accepted
  all_goals try (casesm* core.result.Result Never _ <;> try casesm* Never)
  all_goals repeat' observation_step accepted
  all_goals simp_all
end Itasca.Runtime.Compiler

end

/-! ## ControlObservedLayout -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std


theorem compiler_enter_layout_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (known : ConcreteStack state.vals.val) (locals : LocalLayout after)
    (accepted : runtime.compiler.control.FunctionCompiler.enter ops before state kind bt = .ok (.Ok (), after)) :
    CompilerLayout after (Itasca.Sequence.stackTypes state.vals.val) := by
  obtain ⟨middle, observed⟩ := compiler_enter_observation ops before after state kind bt accepted
  exact compiler_observe_layout_success ops law middle after state known locals observed


theorem compiler_end_layout_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (known : ConcreteStack state.vals.val) (locals : LocalLayout after)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (), after)) :
    CompilerLayout after (Itasca.Sequence.stackTypes state.vals.val) := by
  obtain ⟨middle, observed⟩ := compiler_end_observation ops before after state kind bt accepted
  exact compiler_observe_layout_success ops law middle after state known locals observed


theorem compiler_else_layout_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (known : ConcreteStack state.vals.val) (locals : LocalLayout after)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops before state bt = .ok (.Ok (), after)) :
    CompilerLayout after (Itasca.Sequence.stackTypes state.vals.val) := by
  obtain ⟨middle, observed⟩ := compiler_else_observation ops before after state bt accepted
  exact compiler_observe_layout_success ops law middle after state known locals observed

end Itasca.Runtime.Compiler

end
