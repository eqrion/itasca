import Exec.Abs.Float.Transition
import Exec.Interp.Core.OwnershipClosure
namespace Exec.Interp
open Abs.Ownership

theorem float_transition_frame_ownership (s : _root_.store) (ambient : frame)
    (f g : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (op : Abs.Float.Instruction)
    (step : Abs.Float.Transition ⟨s,ambient,{f with code := op.source :: after}::rest,[]⟩
      {f with code := op.source :: after} rest after op (.next ⟨s,ambient,g::rest,[]⟩)) :
    FrameOwnershipClosure {f with code := op.source :: after} g := by
  cases step with
  | next front a b bits values first second effect =>
    intro bounds owned
    change ValuesOwned bounds f.locals ∧ ValuesOwned bounds
      (front ++ [.CONST op.output (Abs.Float.numberOfBits op.output bits)])
    have old := owned.2
    change ValuesOwned bounds f.vals at old
    change f.vals = front ++ op.operands a b at values
    rw [values] at old
    refine ⟨owned.1,valuesOwned_append.mpr ⟨(valuesOwned_append.mp old).1,?_⟩⟩
    intro value member
    simp only [List.mem_singleton] at member
    subst value
    trivial
end Exec.Interp
