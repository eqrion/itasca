import Exec.Spec.Choices.Steps
import Exec.Theorems.Host.HostWorldSound
import Exec.Theorems.Host.Chosen.HostChoiceMatching
namespace Exec.Theorems
open Aeneas Aeneas.Std

/-- Returning callbacks choose their post-world and match the preselected
source reply at each occurrence. Matching concerns one primitive callback and
its actual dynamic result check, independently of an invocation trace. -/
def HostWorldChosenSound {M P : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (view : M → Slice U8)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop) (choices : Spec.SourceChoices) : Prop :=
  ∀ occurrence code store, Inv code store → ∀ platform identity args defaults,
    hooks.call_host platform store identity args defaults ⦃ answer => ∃ afterCode,
      Store.CodeAgreesOn store code afterCode ∧ Inv afterCode answer.2.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode answer.2.2.1) ∧
      Store_ok (Store.decodeStore view afterCode answer.2.2.1) ∧
      ∀ (address : runtime.FuncAddr) (function : runtime.store.Function) (signature : Itasca.types.FuncType),
        store.funcs.val[address.index.val]?=some function → function.code=.Host identity →
        store.types.val[function.signature.val]?=some signature →
        choices.host occurrence (Store.decodeStore view code store) address.index.val identity.val
          (signature.params.val.map Interp.sourceType) (signature.results.val.map Interp.sourceType)
          (args.val.map Interp.sourceValue)=
            checkedHostReply memory view afterCode answer.2.2.1 signature ⟨answer.2.2.2⟩ answer.1 ⦄

theorem HostWorldChosenSound.erases {M P memory hooks view Inv choices}
    (sound : HostWorldChosenSound (M:=M) (P:=P) memory hooks view Inv choices) : HostWorldSound hooks view Inv := by
  intro code store valid platform identity args defaults
  apply WP.spec_mono (sound 0 code store valid platform identity args defaults)
  rintro answer ⟨afterCode,agrees,fresh,extension,typed,matching⟩
  exact ⟨afterCode,agrees,fresh,extension,typed⟩
end Exec.Theorems
