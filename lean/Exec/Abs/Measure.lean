import Exec.Abs.Step
import Mathlib.Tactic

namespace Itasca.Runtime.Abs

/-- Pending instructions in the active frame. Suspended callers do not affect
the bound on consecutive administrative constant moves; real steps may reset it. -/
def administrativeMeasure (s : AState) : Nat :=
  match s.frames with
  | [] => 0
  | f :: _ => f.code.length

/-- Absorbing one constant into the operand stack strictly decreases the
administrative measure, independently of labels, callers, and value sizes. -/
theorem const_measure_decreases (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (ty : numtype) (value : num_) (after : List instr) :
    administrativeMeasure ⟨s, ambient,
      { f with code := after, vals := f.vals ++ [.CONST ty value] } :: rest, []⟩ <
    administrativeMeasure ⟨s, ambient,
      { f with code := .CONST ty value :: after } :: rest, []⟩ := by
  simp [administrativeMeasure]

end Itasca.Runtime.Abs
