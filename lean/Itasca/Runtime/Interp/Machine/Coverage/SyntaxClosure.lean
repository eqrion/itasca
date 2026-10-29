import Itasca.Runtime.Interp.Machine.Point
import Itasca.Runtime.SourceMachine.SupportedState

/-!
A step keeps the frame's code and labels within the binary instruction grammar.

Main declarations: `SyntaxClosure`. A direct consumer is `Interp.Machine.Control.BranchIfOwned`.
-/

namespace Itasca.Runtime.Interp.Machine
/-- A step keeps the frame's code and labels within the binary instruction grammar. -/
def SyntaxClosure (before after : SourceMachine.AFrame) : Prop :=
  SourceMachine.FrameSupported before → SourceMachine.FrameSupported after

theorem SyntaxClosure.refl (f : SourceMachine.AFrame) : SyntaxClosure f f := fun h => h

theorem SyntaxClosure.tail (f : SourceMachine.AFrame) (op : instr) (after : List instr)
    (locals values : List val) :
    SyntaxClosure { f with code := op :: after } { f with code := after, locals := locals, vals := values } := by
  rintro ⟨code, labels⟩
  exact ⟨fun i hi => code i (List.mem_cons_of_mem _ hi), labels⟩

theorem SyntaxClosure.replace (f : SourceMachine.AFrame) (op next : instr) (after : List instr)
    (locals values : List val) (nextAllowed : SourceMachine.BinaryInstr next) :
    SyntaxClosure { f with code := op :: after } { f with code := next :: after, locals := locals, vals := values } := by
  rintro ⟨code, labels⟩
  refine ⟨?_, labels⟩
  intro i hi
  rcases List.mem_cons.mp hi with rfl | member
  · exact nextAllowed
  · exact code i (List.mem_cons_of_mem _ member)

theorem SyntaxClosure.branch (f : SourceMachine.AFrame) (depth : Nat) (label : SourceMachine.Label)
    (lookup : f.labels[depth]? = some label) (values : List val) :
    SyntaxClosure f { f with code := label.cont ++ label.after, labels := f.labels.drop (depth + 1), vals := values } := by
  rintro ⟨code, labels⟩
  have retained := labels label (List.mem_of_getElem? lookup)
  constructor
  · intro i hi
    rcases List.mem_append.mp hi with member | member
    · exact retained.1 i member
    · exact retained.2 i member
  · intro next member
    exact labels next (List.mem_of_mem_drop member)

end Itasca.Runtime.Interp.Machine
