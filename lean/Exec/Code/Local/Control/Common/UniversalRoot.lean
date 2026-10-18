import Exec.Code.Local.Control.Common.UniversalTerminal
import Exec.Code.Local.Relations.Common.FunctionBodyClose
import Exec.Code.Local.Relations.Common.PrefixClose
namespace Exec.Code
open Aeneas.Std

/-- Final END fixes the root's coordinates and both liveness flags, producing
one admissible future plan from the actual root frame's source metadata. -/
theorem root_frame_plan (code : List Bytecode) (locals returns : List valtype)
    (frame : runtime.compiler.Frame) (target : U32) (normal : Bool)
    (kind : frame.kind = .Body) (noGuard : frame.if_pc = none)
    (height : frame.height.val = slots locals) (width : frame.results.val = slots returns)
    (position : target.val = code.length) :
    FramePlans code.length locals [frame]
      [⟨[], returns, returns, target, target.val, [], [], normal, frame.end_reachable⟩]
      [⟨frame.fixups.val, target⟩] := by
  let label : LabelTarget := ⟨[], returns, returns, target, target.val, [], [], normal, frame.end_reachable⟩
  have future : FrameFuture code.length locals frame label 0#u32 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _; simpa [label, slots] using height
    · intro _; exact width
    · intro _; simpa [kind, label] using width
    · exact Nat.le_of_eq position.symm
    · intro _; exact Nat.le_of_eq position.symm
    · simp [kind]
    · simp [kind]
    · exact fun h => h
    · intros; rfl
    · simp [noGuard]
  have planned := FramePlans.push (FramePlans.nil (length := code.length) (locals := locals)) frame label 0#u32 future
  simpa [frameGroups, noGuard, label] using planned

theorem root_scope_label (scope : SourceScope) (returns : List valtype)
    (target : U32) (normal branch : Bool)
    (form : scope.form = .body) (front : scope.front = []) (results : scope.results = returns) :
    ScopeLabel scope ⟨[], returns, returns, target, target.val, [], [], normal, branch⟩ := by
  refine ⟨front.symm, ?_, results.symm⟩
  simp [SourceScope.branchTypes, form, results]

/-- A live completed body supplies the exact resolved root relation required
by the actual final-END theorem, without a retained body-correctness premise. -/
theorem UniversalPrefix.root_finish {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {types functions returns locals current}
    (invariant : UniversalPrefix compiler types functions returns locals [] current returns)
    (frame : runtime.compiler.Frame) (target : U32)
    (frames : compiler.frames.val = [frame]) (kind : frame.kind = .Body) (noGuard : frame.if_pc = none)
    (height : frame.height.val = slots locals) (width : frame.results.val = slots returns)
    (position : target.val = compiler.function.code.val.length)
    (form : current.form = .body) (front : current.front = []) (params : current.params = [])
    (results : current.results = returns) (start : current.bodyPc = 0) :
    CodeRel types functions returns locals (patchCode compiler.function.code.val frame.fixups.val target)
      [⟨[], returns, returns, target, target.val, [], [], true, frame.end_reachable⟩]
      [] current.source 0 target.val returns := by
  have plans := root_frame_plan compiler.function.code.val locals returns frame target true kind noGuard height width position
  rw [← frames] at plans
  have shape := root_scope_label current returns target true frame.end_reachable form front results
  have code := (invariant.prefixes _ [] _ plans shape .nil).2
  have finished := code.finish (by simp [resolvedCode_length]) (by simp [NormalLive])
  simpa [resolvedCode, SourceScope.input, front, params, start, position] using finished

/-- A terminal root body closes at the actual final PC even when its result
signature is nonempty and the emitted unreachable epilogue returns zero words. -/
theorem UniversalTerminal.root_finish {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {types functions returns locals current}
    (invariant : UniversalTerminal compiler types functions returns locals [] current)
    (frame : runtime.compiler.Frame) (target : U32)
    (frames : compiler.frames.val = [frame]) (kind : frame.kind = .Body) (noGuard : frame.if_pc = none)
    (height : frame.height.val = slots locals) (width : frame.results.val = slots returns)
    (position : target.val = compiler.function.code.val.length)
    (form : current.form = .body) (front : current.front = []) (params : current.params = [])
    (results : current.results = returns) (start : current.bodyPc = 0) :
    CodeRel types functions returns locals (patchCode compiler.function.code.val frame.fixups.val target)
      [⟨[], returns, returns, target, target.val, [], [], false, frame.end_reachable⟩]
      [] current.source 0 target.val returns := by
  have plans := root_frame_plan compiler.function.code.val locals returns frame target false kind noGuard height width position
  rw [← frames] at plans
  have shape := root_scope_label current returns target false frame.end_reachable form front results
  have code := (invariant.prefixes _ [] _ plans shape .nil).2
  have finished := code.finish target.val returns (by omega) (by simp [resolvedCode_length, position])
  simpa [resolvedCode, SourceScope.input, front, params, start, position] using finished

end Exec.Code
