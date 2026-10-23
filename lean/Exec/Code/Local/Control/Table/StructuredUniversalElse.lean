import Exec.Code.Local.Control.Table.StructuredCompletedPrefix
import Exec.Code.Local.Control.Table.StructuredElseSource
import Exec.Code.Local.Control.Common.UniversalTerminal
import Exec.Code.Local.Relations.Common.Prefix
import Exec.Code.Local.Callbacks.Control.ElseSource
import Exec.Code.Local.Callbacks.Control.ElseTransition
import Exec.Code.Local.Callbacks.Common.FramePlanPop
import Exec.Code.Local.Relations.Common.ResolvedGuards
namespace Exec.Code
open Aeneas.Std

/-- ELSE freezes the completed arm under every future outer plan and starts
its sibling body. Both normal and terminal then arms use the same actual
patch/optional-skip transition. -/
theorem StructuredCompletedPrefix.begin_else {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents scope normal}
    (invariant : StructuredCompletedPrefix (jumpTables := jumpTables) emit before types functions returns locals parents scope normal)
    (completed : StructuredUniversalElse (jumpTables := jumpTables) emit before types functions returns locals parents scope)
    (prior : List runtime.compiler.Frame) (frame : runtime.compiler.Frame)
    (guard site : Usize) (condition old noEntry : U32) (fixups : alloc.vec.Vec Usize)
    (change : ElseTransition before after prior frame guard site condition old noEntry fixups normal)
    (bt : blocktype) (form : scope.form = .then_ bt condition)
    (entered : scope.entered = true) (entry : scope.entry = guard.val)
    (bodyStart : scope.bodyPc = scope.entry + 1)
    (conditionSlot : condition.val = slots locals + slots scope.input)
    (kind : frame.kind = .Then) (guardEq : frame.if_pc = some guard)
    (distinct : ∀ other ∈ prior, other.if_pc ≠ some guard)
    (localsEq : compilerLocals after = locals) (layout : CompilerLayout after scope.input) :
    StructuredUniversalPrefix (jumpTables := jumpTables) emit after types functions returns locals parents
      (scope.begin_else bt condition before.function.code.val.length noEntry normal) scope.input ∧
    StructuredUniversalElse (jumpTables := jumpTables) emit after types functions returns locals parents
      (scope.begin_else bt condition before.function.code.val.length noEntry normal) := by
  let next := scope.begin_else bt condition before.function.code.val.length noEntry normal
  have advance : ∀ label labels groups,
      FramePlans after.function.code.val.length locals after.frames.val (label :: labels) groups →
      ScopeLabel next label → List.Forall₂ ScopeLabel parents.reverse labels →
      StructuredParentPrefixes (jumpTables := jumpTables) emit types functions returns locals (resolvedCode after.function.code.val groups) parents labels next ∧
      StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals (resolvedCode after.function.code.val groups)
        (label :: labels) next.input next.source next.bodyPc after.function.code.val.length scope.input ∧
      StructuredElseFrames (jumpTables := jumpTables) emit types functions returns locals (resolvedCode after.function.code.val groups)
        (next :: parents.reverse) (label :: labels) := by
    intro label labels groups plans shape parentShapes
    rw [change.afterFrames] at plans
    obtain ⟨found, outer, pending, ignored, sameLabels, grouped, outerPlans, future⟩ := plans.pop
    have same : found = label ∧ outer = labels := by simpa using sameLabels.symm
    obtain ⟨foundEq, outerEq⟩ := same
    subst found outer
    have groupsEq : groups = ⟨fixups.val, label.target⟩ :: pending := by
      simpa [frameGroups] using grouped
    rw [groupsEq]
    let oldLabel : LabelTarget := {label with normalExit := before.function.code.val.length, cont := [], after := [], normalLive := normal}
    have futureZero : FrameFuture after.function.code.val.length locals
        {frame with kind := .Else, if_pc := none, end_reachable := frame.end_reachable || normal, fixups} label 0#u32 :=
      {future with guardBound := by simp}
    have oldFuture : FrameFuture before.function.code.val.length locals frame oldLabel noEntry :=
      futureZero.before_else normal noEntry kind change.order (by rw [change.noPosition]; omega)
    have oldOuter := outerPlans.before change.order
    have oldPlans := FramePlans.push oldOuter frame oldLabel noEntry oldFuture
    rw [← change.beforeFrames] at oldPlans
    have oldPlans' : FramePlans before.function.code.val.length locals before.frames.val
        (oldLabel :: labels) (⟨[guard], noEntry⟩ :: ⟨frame.fixups.val, label.target⟩ :: pending) := by
      simpa [frameGroups, guardEq, oldLabel] using oldPlans
    have oldShape : ScopeLabel scope oldLabel := by
      have sameShape := shape.before_else form
      exact ⟨sameShape.front, sameShape.branchTypes, sameShape.results⟩
    obtain ⟨saved, body⟩ := invariant.prefixes oldLabel labels _ oldPlans' oldShape parentShapes rfl rfl
    have arms := completed oldLabel labels _ oldPlans' oldShape parentShapes
    have inside : FixupsInside (⟨frame.fixups.val, label.target⟩ :: pending) before.function.code.val.length := by
      intro group member atSite atMember
      exact oldPlans'.inside invariant.sites group (List.mem_cons_of_mem _ member) atSite atMember
    have resolved := change.resolved pending label.target inside
    let emitted : List Bytecode := if normal then [.Jump label.target] else []
    have guardFound : (resolvedCode before.function.code.val
        (⟨[guard], noEntry⟩ :: ⟨frame.fixups.val, label.target⟩ :: pending))[scope.entry]? =
        some (.JumpIfZero condition noEntry) := by
      rw [entry]
      have current := invariant.sites frame (by simp [change.beforeFrames])
      have outerAway := oldOuter.away_guard
        (fun f member => invariant.sites f (by rw [change.beforeFrames]; exact List.mem_append_left _ member))
        change.guardCode distinct
      exact resolvedCode_guard _ [] _ guard condition old noEntry change.guardCode (by
        intro group member atSite atMember
        simp only [List.nil_append, List.mem_cons] at member
        rcases member with rfl | remaining
        · exact current.branches.not_guard change.guardCode atSite atMember
        · exact outerAway group remaining atSite atMember)
    have updatedBody : StructuredCode emit types functions returns locals
        (resolvedCode after.function.code.val (⟨fixups.val, label.target⟩ :: pending)) jumpTables
        (⟨scope.front, scope.results, scope.results, label.target, before.function.code.val.length,
          [], [], normal, label.branchLive⟩ :: labels)
        scope.input scope.source (scope.entry + 1) before.function.code.val.length (scope.front ++ scope.results) := by
      rw [resolved]
      have labelEq : oldLabel = ⟨scope.front, scope.results, scope.results, label.target,
          before.function.code.val.length, [], [], normal, label.branchLive⟩ := by
        have branchEq : oldLabel.branchTypes = scope.results := by
          simpa [SourceScope.branchTypes, form] using oldShape.branchTypes
        have frontEq : label.front = scope.front := oldShape.front
        have resultEq : label.resultTypes = scope.results := oldShape.results
        have branchEq' : label.branchTypes = scope.results := branchEq
        simp only [oldLabel, frontEq, resultEq, branchEq']
      simpa only [labelEq, bodyStart] using body.extend emitted
    have skip : IfSkip (resolvedCode after.function.code.val (⟨fixups.val, label.target⟩ :: pending))
        before.function.code.val.length noEntry label.target normal := by
      rw [resolved]
      exact .emitted ⟨resolvedCode before.function.code.val
        (⟨[guard], noEntry⟩ :: ⟨frame.fixups.val, label.target⟩ :: pending), [],
        by simp, resolvedCode_length _ _, by
          cases normal <;> simpa using change.noPosition⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [resolved]
      exact (saved.extend emitted).change_current rfl rfl
        (scope.begin_else_arguments bt condition _ noEntry normal form)
    · simpa only [next, SourceScope.begin_else, SourceScope.input, change.length] using
        StructuredPrefix.empty emit types functions returns locals
          (resolvedCode after.function.code.val (⟨fixups.val, label.target⟩ :: pending))
          (label :: labels) scope.input noEntry.val
    · refine .cons next label ?_ ?_
      · apply StructuredElseEvidence.begin_else entered conditionSlot
        · rw [resolved]; exact fetch_extend guardFound emitted
        · exact updatedBody
        · exact skip
      · rw [resolved]
        exact arms.outer.extend emitted
  refine ⟨⟨localsEq, layout, change.sites invariant.sites, ?_⟩, ?_⟩
  · intro label labels groups plans shape parentShapes
    have outcome := advance label labels groups plans shape parentShapes
    exact ⟨outcome.1, outcome.2.1⟩
  · intro label labels groups plans shape parentShapes
    exact (advance label labels groups plans shape parentShapes).2.2

end Exec.Code

