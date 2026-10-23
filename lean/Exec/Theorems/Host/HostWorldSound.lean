import Exec.Theorems.Composition.ExecutionCode
import Exec.Platform.HostSound
import Exec.Contracts
namespace Exec.Theorems
open Aeneas Aeneas.Std

/-- Fixed-world host soundness is a special case of the indexed contract;
this lemma makes no claim that arbitrary hosts satisfy either contract. -/
theorem HostWorldSound.of_fixed {M P : Type} {hooks : runtime.platform.Platform P M}
    {view : M → Slice U8} {Inv : Store.CodeInterpretation → runtime.store.Store M → Prop}
    (sound : ∀ code, Platform.HostSound hooks (Inv code) (Store.decodeStore view code)) :
    HostWorldSound hooks view Inv := by
  intro code store valid platform host args results
  apply WP.spec_mono ((sound code).host platform store host args results valid)
  intro answer outcome
  exact ⟨code,(by intro index inst found fn; rfl),outcome⟩
end Exec.Theorems
