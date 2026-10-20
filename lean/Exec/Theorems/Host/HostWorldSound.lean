import Exec.Theorems.Composition.ExecutionCode
import Exec.Platform.HostSound
namespace Exec.Theorems
open Aeneas Aeneas.Std

/-- The callback contract carries its current ghost interpretation explicitly.
Its returned interpretation agrees on previously issued keys; fresh keys are
chosen by publication. Raw metadata retention remains a separate hypothesis. -/
def HostWorldSound {M P : Type} (hooks : runtime.platform.Platform P M)
    (view : M → Slice U8) (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀ code store, Inv code store → ∀ platform host args results,
    hooks.call_host platform store host args results ⦃ answer => ∃ afterCode,
      Store.CodeAgreesOn store code afterCode ∧ Inv afterCode answer.2.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode answer.2.2.1) ∧
        Store_ok (Store.decodeStore view afterCode answer.2.2.1) ⦄

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
