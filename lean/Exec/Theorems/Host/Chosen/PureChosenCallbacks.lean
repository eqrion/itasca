import Exec.Theorems.Host.Callbacks.PureCallbacks
import Exec.Theorems.Host.Chosen.HostWorldChosenSound
import Exec.Theorems.Composition.World.ChosenWorldResourceBounds
namespace Exec.Theorems.PureCallbacks
open Aeneas Aeneas.Std

/-- This actual callback has the independently specified trapping source reply.
The invariant may include configured resource floors: the store is unchanged. -/
theorem trapping_chosen_sound {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (typed : ∀code store,Inv code store → Store_ok (Store.decodeStore view code store))
    (choices : Spec.SourceChoices) (selected : choices.host=Spec.trappingHostChoice) :
    HostWorldChosenSound memory (platform memory (fun _ _=>.trapped)) view Inv choices := by
  intro occurrence code store held token identity args defaults
  have sourceTyped := typed code store held
  have wellFormed : wf_store (Store.decodeStore view code store) := by cases sourceTyped; assumption
  refine WP.spec.ret ⟨code,(by intro index inst found fn; rfl),held,Spec.extend_store_refl _ wellFormed,sourceTyped,?_⟩
  intro address function signature hf kind hs
  simp [selected,Spec.trappingHostChoice,checkedHostReply,Program.evaluate]

/-- The executable trapping callback cannot report host stack exhaustion. -/
theorem trapping_no_stack_overflow {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop) :
    NoHostStackOverflow (platform memory (fun _ _=>.trapped)) Inv := by
  intro code store held token identity args defaults nextToken after results
  simp [platform,Program.evaluate]
end Exec.Theorems.PureCallbacks
