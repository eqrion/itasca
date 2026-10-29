import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalTerminal
import Itasca.Runtime.Compiler.Local.Callbacks.Function.CloseFunction
import Itasca.Runtime.Compiler.Local.Relations.Function.Function
import Itasca.Runtime.Compiler.Local.Relations.Prefix.LabelWiden
import Itasca.Runtime.Compiler.Local.Relations.Prefix.Extension
import Itasca.Runtime.Compiler.Local.Relations.Prefix.Prefix

/-!
Final END fixes the root's coordinates and both liveness flags, producing one admissible future plan from the actual root frame's source metadata.

Main declarations: `root_frame_plan` and `root_scope_label`. A direct consumer is `Compiler.Local.Control.Table.StructuredUniversalCloseBlock`.
-/

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler
