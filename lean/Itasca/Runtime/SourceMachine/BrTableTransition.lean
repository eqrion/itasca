import Itasca.Runtime.SourceMachine.BrTable
import Itasca.Runtime.SourceMachine.Cumulative.Heap
import Itasca.Runtime.SourceMachine.Supported.CoreStuck
import Itasca.Runtime.SourceMachine.Bound

/-!
Branch-table transitions with ownership and code-bound preservation. Basic branch-table source semantics remain below the stateful invariant imports.
-/

/-! ## Br Table Invariants -/

section

namespace Itasca.Runtime.Abs.BrTable
open Ownership

/-- Selecting a label only removes the integer selector; all owned references
and every source heap component are retained. -/
theorem owned {bounds : Bounds} {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
    {after : List instr} {labels : List labelidx} {fallback : labelidx} {front : List val} {bits : Nat}
    (before : StatefulOwned bounds ⟨s,ambient,{f with code := .BR_TABLE labels fallback::after,vals := front ++ [integerVal .I32 bits]}::rest,[]⟩) :
    StatefulOwned bounds ⟨s,ambient,{f with code := .BR (select labels fallback bits)::after,vals := front}::rest,[]⟩ := by
  have frame := before.values.2 _ (List.mem_cons_self ..)
  apply stateful_owned_advance (step := rfl) before.heap (valuesOwned_nil _) ?_ ?_
  · exact ⟨frame.1,(valuesOwned_append.mp frame.2).1⟩
  · exact fun item member => before.values.2 item (List.mem_cons_of_mem _ member)

theorem bounded {bound : Nat} {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
    {after : List instr} {labels : List labelidx} {fallback : labelidx} {front : List val} {bits : Nat}
    (before : CodeBound bound ⟨s,ambient,{f with code := .BR_TABLE labels fallback::after,vals := front ++ [integerVal .I32 bits]}::rest,[]⟩) :
    CodeBound bound ⟨s,ambient,{f with code := .BR (select labels fallback bits)::after,vals := front}::rest,[]⟩ := by
  apply bound_replace_frame before
  have frame := before.frames _ (List.mem_cons_self ..)
  refine ⟨?_,frame.2⟩
  have size := frame.1
  have selected := select_size labels fallback bits
  simp at size ⊢
  omega

theorem covered
    {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
    {after : List instr} {labels : List labelidx} {fallback : labelidx} {front : List val} {bits : Nat}
    (before : SupportedState ⟨s,ambient,{f with code := .BR_TABLE labels fallback::after,vals := front ++ [integerVal .I32 bits]}::rest,[]⟩) :
    SupportedState ⟨s,ambient,{f with code := .BR (select labels fallback bits)::after,vals := front}::rest,[]⟩ := by
  have frame := before.active _ (List.mem_cons_self ..)
  refine ⟨?_,before.functions⟩
  intro item member
  rcases List.mem_cons.mp member with rfl | member
  · refine ⟨?_,frame.2⟩
    intro instruction member
    rcases List.mem_cons.mp member with rfl | member
    · exact Abs.BinaryInstr.br _
    · exact frame.1 instruction (List.mem_cons_of_mem _ member)
  · exact before.active item (List.mem_cons_of_mem _ member)
end Itasca.Runtime.Abs.BrTable

end

/-! ## Br Table Transition -/

section

namespace Itasca.Runtime.Abs.BrTable
open SpecExt Itasca.Runtime.Spec Ownership

inductive Transition : AState → AState → Prop where
  | next {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
      {after : List instr} {labels : List labelidx} {fallback : labelidx} {front : List val} {bits : Nat}
      (values : f.vals = front ++ [integerVal .I32 bits]) (bound : bits < 2^32) :
      Transition ⟨s,ambient,{f with code := .BR_TABLE labels fallback::after}::rest,[]⟩
        ⟨s,ambient,{f with code := .BR (select labels fallback bits)::after,vals := front}::rest,[]⟩

private theorem normalized {f : AFrame} {source : List instr} {values : List val}
    (same : f.vals = values) : {f with code := source,vals := values} = {f with code := source} := by
  cases f
  simp_all

theorem Transition.correct {before next} (transition : Transition before next) (typed : CoreTyped before) :
    CoreTyped next ∧ NextSim before next := by
  cases transition with
  | @next s ambient f rest after labels fallback front bits values bound =>
    have result := BrTable.correct s ambient f rest after front bits labels fallback bound
      (by simpa only [normalized values] using typed.typed)
    exact ⟨⟨result.1,typed.contents⟩,by simpa only [normalized values] using result.2⟩

theorem Transition.next_supported {before next}
    (transition : Transition before next) (supported : SupportedState before) : SupportedState next := by
  cases transition with
  | next values bound =>
    exact covered (by simpa only [normalized values] using supported)

theorem Transition.next_owned {bounds before next} (transition : Transition before next)
    (initial : StatefulOwned bounds before) : StatefulOwned bounds next := by
  cases transition with
  | next values bound => exact owned (by simpa only [normalized values] using initial)

theorem Transition.next_bound {bound before next} (transition : Transition before next)
    (initial : CodeBound bound before) : CodeBound bound next := by
  cases transition with
  | next values bound => exact bounded (by simpa only [normalized values] using initial)

end Itasca.Runtime.Abs.BrTable

end
