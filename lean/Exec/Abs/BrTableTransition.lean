import Exec.Abs.BrTableInvariants

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

