import Exec.Spec.Open.ExecutionChoices
import Exec.Spec.Choices.ChosenCounted
namespace Exec.Spec.OpenExecution
open SpecExt

theorem ChoiceTrace.trans {H : Type} {model : HostModel H} {choices : Choices H}
    {occurrence count more first middle last events observed}
    (head : ChoiceTrace model choices occurrence count first events middle)
    (tail : ChoiceTrace model choices (occurrence+count) more middle observed last) :
    ChoiceTrace model choices occurrence (count+more) first (events++observed) last := by
  induction head with
  | nil occurrence state=>simpa only [Nat.add_zero,Nat.zero_add,List.nil_append] using tail
  | @next occurrence count first middle endpoint events more step rest ih=>
    have final:=ih (by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using tail)
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc] using ChoiceTrace.next step final

/-- A silent fixed-policy Wasm prefix embeds in combined execution without
changing its occurrence count or erasing its source reductions. -/
theorem ChoiceTrace.wasmCounted {H : Type} (model : HostModel H) (choices : Choices H)
    {occurrence count : Nat} {first last : config}
    (steps : ChosenStepsN choices.wasm occurrence count first [] last) (expected : resulttype)
    (stack : List (Continuation H)) :
    ChoiceTrace model choices occurrence count ⟨first.1.1,.wasm first.1.2 first.2 expected,stack⟩
      (List.replicate count .wasm) ⟨last.1.1,.wasm last.1.2 last.2 expected,stack⟩ := by
  generalize empty : ([] : List HostEvent)=events at steps
  induction steps with
  | refl occurrence wf=>exact .nil _ _
  | @cons occurrence count first middle last headEvents tailEvents head tail ih=>
    obtain ⟨rfl,rfl⟩:=List.append_eq_nil_iff.mp empty.symm
    have rest:=ih rfl
    rcases first with ⟨⟨s,f⟩,body⟩
    rcases middle with ⟨⟨t,g⟩,after⟩
    simpa only [List.replicate_succ,List.singleton_append] using ChoiceTrace.next (ChoiceTransition.wasm head) rest

theorem ChoiceInfinite.uncons {H : Type} {model : HostModel H} {choices : Choices H} {occurrence first}
    (infinite : ChoiceInfinite model choices occurrence first) :
    ∃events middle,ChoiceTransition model choices occurrence first events middle ∧ ChoiceInfinite model choices (occurrence+1) middle := by
  obtain ⟨states,events,initial,steps⟩:=infinite
  refine ⟨events 0,states 1,?_,fun n=>states (n+1),fun n=>events (n+1),rfl,?_⟩
  · simpa only [initial,Nat.add_zero] using steps 0
  · intro n
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using steps (n+1)
end Exec.Spec.OpenExecution
