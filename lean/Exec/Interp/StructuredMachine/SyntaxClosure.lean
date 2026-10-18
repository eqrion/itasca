import Exec.Interp.StructuredMachine.Point
namespace Exec.Interp.StructuredMachine
/-- The source instructions retained in an active frame and its labels. -/
def FrameSyntax (allowed : instr → Prop) (f : Abs.AFrame) : Prop :=
  Forall allowed f.code ∧ Forall (fun label => Forall allowed label.cont ∧ Forall allowed label.after) f.labels

/-- Syntax preservation is independent of the particular cumulative grammar. -/
def SyntaxClosure (allowed : instr → Prop) (before after : Abs.AFrame) : Prop :=
  FrameSyntax allowed before → FrameSyntax allowed after

variable {allowed : instr → Prop}
theorem SyntaxClosure.refl (f : Abs.AFrame) : SyntaxClosure allowed f f := fun h => h

theorem SyntaxClosure.trans {before middle after} (first : SyntaxClosure allowed before middle)
    (second : SyntaxClosure allowed middle after) : SyntaxClosure allowed before after := fun h => second (first h)

theorem SyntaxClosure.tail (f : Abs.AFrame) (op : instr) (after : List instr)
    (locals values : List val) :
    SyntaxClosure allowed { f with code := op :: after } { f with code := after, locals := locals, vals := values } := by
  rintro ⟨code, labels⟩
  exact ⟨fun i hi => code i (List.mem_cons_of_mem _ hi), labels⟩

theorem SyntaxClosure.replace (f : Abs.AFrame) (op next : instr) (after : List instr)
    (locals values : List val) (nextAllowed : allowed next) :
    SyntaxClosure allowed { f with code := op :: after } { f with code := next :: after, locals := locals, vals := values } := by
  rintro ⟨code, labels⟩
  refine ⟨?_, labels⟩
  intro i hi
  rcases List.mem_cons.mp hi with rfl | member
  · exact nextAllowed
  · exact code i (List.mem_cons_of_mem _ member)

theorem SyntaxClosure.branch (f : Abs.AFrame) (depth : Nat) (label : Abs.Label)
    (lookup : f.labels[depth]? = some label) (values : List val) :
    SyntaxClosure allowed f { f with code := label.cont ++ label.after, labels := f.labels.drop (depth + 1), vals := values } := by
  rintro ⟨code, labels⟩
  have retained := labels label (List.mem_of_getElem? lookup)
  constructor
  · intro i hi
    rcases List.mem_append.mp hi with member | member
    · exact retained.1 i member
    · exact retained.2 i member
  · intro next member
    exact labels next (List.mem_of_mem_drop member)


end Exec.Interp.StructuredMachine
