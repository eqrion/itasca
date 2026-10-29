import Itasca.Runtime.SourceMachine.Float.Transition
import Itasca.Runtime.Interp.Machine.Retention.Ownership
namespace Itasca.Runtime.Interp
open SourceMachine.Ownership

theorem float_transition_frame_ownership (s : _root_.store) (ambient : frame)
    (f g : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (op : SourceMachine.Float.Instruction)
    (step : SourceMachine.Float.Transition ⟨s,ambient,{f with code := op.source :: after}::rest,[]⟩
      {f with code := op.source :: after} rest after op (.next ⟨s,ambient,g::rest,[]⟩)) :
    FrameOwnershipClosure {f with code := op.source :: after} g := by
  cases step with
  | next front a b bits values first second effect =>
    intro bounds owned
    change ValuesOwned bounds f.locals ∧ ValuesOwned bounds
      (front ++ [.CONST op.output (SourceMachine.Float.numberOfBits op.output bits)])
    have old := owned.2
    change ValuesOwned bounds f.vals at old
    change f.vals = front ++ op.operands a b at values
    rw [values] at old
    refine ⟨owned.1,values_owned_append.mpr ⟨(values_owned_append.mp old).1,?_⟩⟩
    intro value member
    simp only [List.mem_singleton] at member
    subst value
    trivial
end Itasca.Runtime.Interp
