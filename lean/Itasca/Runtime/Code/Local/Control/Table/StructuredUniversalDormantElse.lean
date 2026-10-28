import Itasca.Runtime.Code.Local.Control.Table.StructuredUniversalDormant
import Itasca.Runtime.Code.Local.Control.Table.StructuredElseSource
import Itasca.Runtime.Code.Local.Control.Common.UniversalDormant
import Itasca.Runtime.Code.Local.Control.Common.UniversalTerminal
import Itasca.Runtime.Code.Local.Relations.Common.Prefix
import Itasca.Runtime.Code.Local.Callbacks.Control.ElseSource
import Itasca.Runtime.Code.Local.Callbacks.Control.ElseTransition
import Itasca.Runtime.Code.Local.Callbacks.Common.FramePlanPop
import Itasca.Runtime.Code.Local.Relations.Common.ResolvedGuards
namespace Itasca.Runtime.Code
open Aeneas.Std

/-- An omitted IF arm changes only the source cursor and frame kind at ELSE.
Its parents retain their prefixes, without assigning code to either omitted arm. -/
theorem StructuredUniversalDormant.begin_else {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents scope}
    (invariant : StructuredUniversalDormant (jumpTables := jumpTables) emit before types functions returns locals parents scope)
    (completed : StructuredUniversalElse (jumpTables := jumpTables) emit before types functions returns locals parents scope)
    (prior : List runtime.compiler.Frame) (frame : runtime.compiler.Frame)
    (beforeFrames : before.frames.val = prior ++ [frame])
    (afterFrames : after.frames.val = prior ++ [{frame with kind := .Else, if_pc := none}])
    (kind : frame.kind = .Then) (noGuard : frame.if_pc = none)
    (codeEq : after.function.code = before.function.code)
    (localsEq : compilerLocals after = locals)
    (bt : blocktype) (condition noEntry : U32) (yesExit : Nat) (normal : Bool)
    (form : scope.form = .then_ bt condition) :
    StructuredUniversalDormant (jumpTables := jumpTables) emit after types functions returns locals parents
      (scope.begin_else bt condition yesExit noEntry normal) ∧
    StructuredUniversalElse (jumpTables := jumpTables) emit after types functions returns locals parents
      (scope.begin_else bt condition yesExit noEntry normal) := by
  let next := scope.begin_else bt condition yesExit noEntry normal
  have previous : ∀ label labels groups,
      FramePlans after.function.code.val.length locals after.frames.val (label :: labels) groups →
      FramePlans before.function.code.val.length locals before.frames.val (label :: labels) groups := by
    intro label labels groups plans
    rw [afterFrames] at plans
    obtain ⟨top, outer, pending, target, sameLabels, grouped, outerPlans, future⟩ := plans.pop
    have same : top = label ∧ outer = labels := by simpa using sameLabels.symm
    obtain ⟨topEq, outerEq⟩ := same
    subst top outer
    have oldFuture : FrameFuture before.function.code.val.length locals frame label target := by
      refine ⟨future.height, future.results, ?_, ?_, ?_, ?_, ?_, future.marked, ?_, ?_⟩
      · simpa [kind] using future.branchWidth
      · simpa only [codeEq] using future.normalBound
      · intro _; simpa only [codeEq] using future.forwardBound (by simp)
      · simp [kind]
      · simp [kind]
      · simp [kind]
      · simp [noGuard]
    have oldOuter : FramePlans before.function.code.val.length locals prior labels pending := by
      simpa only [codeEq] using outerPlans
    have result := FramePlans.push oldOuter frame label target oldFuture
    rw [← beforeFrames] at result
    have groupsEq : groups = frameGroups frame label target ++ pending := by
      simpa [frameGroups, noGuard] using grouped
    simpa only [groupsEq] using result
  refine ⟨⟨invariant.unentered, localsEq, ?_, ?_⟩, ?_⟩
  · intro f member
    rw [afterFrames] at member
    rcases List.mem_append.mp member with old | fresh
    · simpa only [codeEq] using invariant.sites f (by rw [beforeFrames]; exact List.mem_append_left _ old)
    · simp only [List.mem_singleton] at fresh
      subst f
      have sites := invariant.sites frame (by simp [beforeFrames])
      exact ⟨by simpa only [codeEq] using sites.branches, by simp⟩
  · intro label labels groups plans shape parentShapes
    have oldShape := shape.before_else form
    have saved := invariant.prefixes label labels groups (previous label labels groups plans) oldShape parentShapes
    simpa only [codeEq] using saved.change_current (after := next) rfl rfl
      (scope.begin_else_arguments bt condition yesExit noEntry normal form)
  · intro label labels groups plans shape parentShapes
    have arms := completed label labels groups (previous label labels groups plans)
      (shape.before_else form) parentShapes
    refine .cons next label ?_ ?_
    · simp [StructuredElseEvidence, next, SourceScope.begin_else, invariant.unentered]
    · simpa only [codeEq] using arms.outer

end Itasca.Runtime.Code
