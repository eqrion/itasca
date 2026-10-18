import Exec.Abs.BrTableInvariants

namespace Exec.Abs.BrTable
open SpecExt Exec.Spec Ownership

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

theorem Transition.of_run {s ambient f rest after labels fallback next}
    (typed : CoreTyped ⟨s,ambient,{f with code := .BR_TABLE labels fallback::after}::rest,[]⟩)
    (equation : step ⟨s,ambient,{f with code := .BR_TABLE labels fallback::after}::rest,[]⟩
      f rest after labels fallback = .next next) :
    Transition ⟨s,ambient,{f with code := .BR_TABLE labels fallback::after}::rest,[]⟩ next := by
  have ft : FrameTyped s {f with code := .BR_TABLE labels fallback::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨front,bits,values,bound⟩ := operands ft
  have accept : integer .I32 (integerVal .I32 bits) = some bits := by
    simpa only [numtype_Inn] using integer_accepts .I32 bits bound
  simp only [step,values,pop_append,accept,advance,AResult.next.injEq] at equation
  cases equation
  exact .next values bound

theorem Transition.correct {before next} (transition : Transition before next) (typed : CoreTyped before) :
    CoreTyped next ∧ NextSim before next := by
  cases transition with
  | @next s ambient f rest after labels fallback front bits values bound =>
    have result := BrTable.correct s ambient f rest after front bits labels fallback bound
      (by simpa only [normalized values] using typed.typed)
    exact ⟨⟨result.1,typed.contents⟩,by simpa only [normalized values] using result.2⟩

theorem Transition.next_supported {allowed before next} (language : Supported.Language allowed)
    (transition : Transition before next) (supported : SupportedState allowed before) : SupportedState allowed next := by
  cases transition with
  | next values bound =>
    exact covered language (by simpa only [normalized values] using supported)

theorem Transition.next_owned {bounds before next} (transition : Transition before next)
    (initial : StatefulOwned bounds before) : StatefulOwned bounds next := by
  cases transition with
  | next values bound => exact owned (by simpa only [normalized values] using initial)

theorem Transition.next_bound {bound before next} (transition : Transition before next)
    (initial : CodeBound bound before) : CodeBound bound next := by
  cases transition with
  | next values bound => exact bounded (by simpa only [normalized values] using initial)

theorem Transition.metadata {before next} (transition : Transition before next) :
    next.store = before.store ∧ next.ambient = before.ambient := by
  cases transition
  exact ⟨rfl,rfl⟩

end Exec.Abs.BrTable

