import Exec.Spec.Open.ExecutionTraces
import Exec.Spec.Counted
namespace Exec.Spec.OpenExecution
open SpecExt

theorem State.wasm_eq {H : Type} (state : State H) (configuration : config) (expected : resulttype)
    (storeEq : state.store=configuration.1.1)
    (modeEq : state.mode=.wasm configuration.1.2 configuration.2 expected) :
    state=⟨configuration.1.1,.wasm configuration.1.2 configuration.2 expected,state.stack⟩ := by
  rcases state with ⟨s,mode,stack⟩
  dsimp only at storeEq modeEq ⊢
  subst s
  subst mode
  rfl

/-- Counted silent source reductions keep their exact positive length when
embedded in the combined machine. Administrative native stutters remain the
separate zero-length case of the ranked refinement. -/
theorem Trace.wasmCounted {H : Type} (model : HostModel H) {count : Nat} {first last : config}
    (steps : StepsHN count first [] last) (expected : resulttype) (stack : List (Continuation H)) :
    Trace model count ⟨first.1.1,.wasm first.1.2 first.2 expected,stack⟩
      (List.replicate count .wasm) ⟨last.1.1,.wasm last.1.2 last.2 expected,stack⟩ := by
  generalize empty : ([] : List HostEvent)=events at steps
  induction steps with
  | refl wf=>exact .nil _
  | @cons count first middle last headEvents tailEvents head tail ih=>
    obtain ⟨rfl,rfl⟩ := List.append_eq_nil_iff.mp empty.symm
    have rest:=ih rfl
    rcases first with ⟨⟨s,f⟩,body⟩
    rcases middle with ⟨⟨t,g⟩,after⟩
    simpa only [List.replicate_succ,List.singleton_append] using Trace.next (Transition.wasm head) rest
end Exec.Spec.OpenExecution
