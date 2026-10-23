import Exec.Spec.Choices.Steps
import Exec.Theorems.Host.HostWorldSound
import Exec.Theorems.Host.Chosen.HostChoiceMatching
import Exec.Contracts
namespace Exec.Theorems
open Aeneas Aeneas.Std

theorem HostWorldChosenSound.erases {M P memory hooks view Inv choices}
    (sound : HostWorldChosenSound (M:=M) (P:=P) memory hooks view Inv choices) : HostWorldSound hooks view Inv := by
  intro code store valid platform identity args defaults
  apply WP.spec_mono (sound 0 code store valid platform identity args defaults)
  rintro answer ⟨afterCode,agrees,fresh,extension,typed,matching⟩
  exact ⟨afterCode,agrees,fresh,extension,typed⟩
end Exec.Theorems
