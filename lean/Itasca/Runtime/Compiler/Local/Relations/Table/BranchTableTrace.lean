import Itasca.Runtime.Compiler.Local.Callbacks.Control.BranchTableCallbacks
import Itasca.Runtime.Compiler.Local.Lowering.Control.TableBranchContracts
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CompilerCodeMonotoneCallbacks
import Itasca.Runtime.Compiler.Local.Relations.Table.TableDepths
import Itasca.Runtime.Compiler.Local.Source.SourceEntry
import Itasca.Runtime.Compiler.Local.Source.SourceCursorTactic

/-!
Sections, each formerly its own module: TableSources, BranchTableTrace.
-/

/-! ## TableSources -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
theorem compiler_table_branch_sources {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize)
    (accepted : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (.Ok (), after)) :
    SourceProgress before after := by
  obtain ⟨answer, current, called, rest⟩ :=
    runtime.compiler.control.FunctionCompiler.table_branch.inv ops before after index (.Ok ()) accepted
  have pc := compiler_pc ops before
  rw [called, WP.spec_ok] at pc
  obtain ⟨budget, same⟩ := pc.2.2
  change current = {before with budget} at same
  subst current
  cases answer with
  | Err error => cases rest.1
  | Ok target =>
    obtain ⟨answer, budget, table, _, rest⟩ := rest
    cases answer with
    | Err error => cases rest.1
    | Ok value =>
      cases value
      obtain ⟨depth, _, branch⟩ := rest
      let staged : runtime.compiler.FunctionCompiler A :=
        {before with budget, function := {before.function with jump_tables := table}}
      change runtime.compiler.control.FunctionCompiler.branch ops staged depth 1#u32 false = .ok (.Ok (), after) at branch
      exact compiler_branch_sources ops law staged after depth 1#u32 false branch

theorem compiler_table_loop_sources {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    (before : runtime.compiler.FunctionCompiler A) (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (output : CompilerSnapshot A)
    (accepted : runtime.compiler.control.FunctionCompiler.lower_table_branches_loop
      ops before index status = .ok output) :
    snapshotStatus output = .Ok () →
      status = .Ok () ∧ SourceProgress before (snapshotCompiler output) := by
  have effect := runtime.compiler.control.FunctionCompiler.lower_table_branches_loop.inv ops before index status output accepted
  clear accepted
  generalize position : index.val = start at effect ⊢
  clear position index
  induction effect with
  | done before index status finished =>
    intro successful
    exact ⟨successful, SourceProgress.refl before⟩
  | step index inside called rest ih =>
    intro successful
    obtain ⟨resultOk, sources⟩ := ih successful
    rw [resultOk] at called
    exact ⟨rfl, (compiler_table_branch_sources ops law _ _ index called).trans sources⟩

theorem compiler_lower_table_sources {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.lower_table_branches ops before = .ok (.Ok (), after)) :
    SourceProgress before after := by
  obtain ⟨start, length, selector, middle, output, _, _, _, emitted, loopCall, successful, same⟩ :=
    (runtime.compiler.control.FunctionCompiler.lower_table_branches.inv ops before after (.Ok ()) accepted).success law
  have final := (compiler_table_loop_sources ops law middle 0#usize (.Ok ()) output loopCall successful).2
  rw [same] at final
  have first : SourceProgress before middle := by
    obtain ⟨_, count, code, sources⟩ := emitted.branch_sources
    have lengths := congrArg List.length sources
    simp only [List.length_map, List.length_append, List.length_replicate] at lengths
    unfold SourceProgress
    omega
  exact first.trans final

theorem compiler_table_label_source_frame {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label
      ops before state depth = .ok (status, after)) :
    SourceStartFrame before after := by
  rw [(runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label.inv ops before after state depth status accepted).frame]
  rfl

theorem compiler_br_table_sources {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (default : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state default types = .ok (.Ok (), after)) :
    SourceProgress before after ∧ after.next_source = state.pos := by
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table.inv ops before after state default types (.Ok ()) accepted with
  | @live labeled lowered cleared _ _ labelCall reachable lowerCall clearCall observed =>
    have labeledSources := (compiler_table_label_source_frame ops before labeled state default (.Ok ()) labelCall).sources
    have loweredSources := compiler_lower_table_sources ops law labeled lowered lowerCall
    exact ⟨labeledSources.trans (loweredSources.trans
      (compiler_observe_sources ops law {lowered with reachable := false, table_depths := cleared} after state (.Ok ()) observed)),
      compiler_observe_cursor ops law {lowered with reachable := false, table_depths := cleared} after state (.Ok ()) observed rfl⟩
  | @dead labeled cleared _ _ labelCall dead clearCall observed =>
    have labeledSources := (compiler_table_label_source_frame ops before labeled state default (.Ok ()) labelCall).sources
    exact ⟨labeledSources.trans
      (compiler_observe_sources ops law {labeled with table_depths := cleared} after state (.Ok ()) observed),
      compiler_observe_cursor ops law {labeled with table_depths := cleared} after state (.Ok ()) observed rfl⟩

end Itasca.Runtime.Compiler

end

/-! ## BranchTableTrace -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
/-- Exact finite callback trace of the target loop. This intermediate execution
witness is eliminated when producing the final syntax-only table certificate. -/
inductive TableBranchRun {A : Type} (ops : runtime.platform.Alloc A) :
    runtime.compiler.FunctionCompiler A → Nat → runtime.compiler.FunctionCompiler A → Prop where
  | done (compiler) (index) (finished : compiler.table_depths.val.length ≤ index) :
      TableBranchRun ops compiler index compiler
  | cons {before middle after} (index : Usize)
      (inside : index.val < before.table_depths.val.length)
      (called : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (.Ok (),middle))
      (rest : TableBranchRun ops middle (index.val+1) after) :
      TableBranchRun ops before index.val after

theorem compiler_table_loop_trace {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    (before : runtime.compiler.FunctionCompiler A) (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (output : CompilerSnapshot A)
    (accepted : runtime.compiler.control.FunctionCompiler.lower_table_branches_loop
      ops before index status = .ok output) :
    snapshotStatus output = .Ok () →
      status = .Ok () ∧ TableBranchRun ops before index.val (snapshotCompiler output) := by
  have effect := runtime.compiler.control.FunctionCompiler.lower_table_branches_loop.inv ops before index status output accepted
  clear accepted
  generalize position : index.val = start at effect ⊢
  clear position index
  induction effect with
  | done before index status finished =>
    intro successful
    change status = .Ok () at successful
    subst status
    rcases finished with outside | impossible
    · exact ⟨rfl, .done before index outside⟩
    · exact False.elim (impossible rfl)
  | step index inside called rest ih =>
    intro successful
    obtain ⟨resultOk, tail⟩ := ih successful
    rw [resultOk] at called
    exact ⟨rfl, .cons index inside called tail⟩

end Itasca.Runtime.Compiler

end
