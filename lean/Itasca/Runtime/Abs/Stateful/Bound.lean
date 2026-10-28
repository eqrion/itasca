import Itasca.Runtime.Abs.Stateful.Metadata
import Itasca.Runtime.Abs.Bound
namespace Itasca.Runtime.Abs.Stateful

theorem transition_bound (bound : Nat) (op : Instruction) (s : store) (ambient : frame)
    (f : AFrame) (rest : List AFrame) (after : List instr) (next : AState)
    (bounded : CodeBound bound ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩)
    (step : Transition ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ f rest after op (.next next)) :
    CodeBound bound next := by
  obtain ⟨values,frames,_,_⟩ := transition_frame _ _ _ _ _ _ step
  have functions := transition_functions _ _ _ _ _ _ step
  have active := bounded.frames {f with code := op.source::after} (List.mem_cons_self ..)
  refine ⟨bounded.positive,?_,?_⟩
  · rw [frames]
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · refine ⟨?_,active.2⟩
      have headBound : sizeOf (op.source::after) ≤ bound := active.1
      simp only [List.cons.sizeOf_spec] at headBound
      change sizeOf after ≤ bound
      omega
    · exact bounded.frames frame (List.mem_cons_of_mem _ member)
  · simpa only [functions] using bounded.functions
end Itasca.Runtime.Abs.Stateful
