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

end Exec.Spec.OpenExecution
