import Exec.Theorems.Api.ExecutableInv
import Exec.Theorems.Composition.Eventful.EventfulWorld
import Exec.Theorems.Composition.Stateful.StatefulOwnership
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Terminal value states have the same certified machine representation as
completed Wasm bodies. This also covers a successful root host invocation. -/
theorem terminal_execution {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (exec : runtime.interp.Execution) (ambient : frame) (ambientWf : wf_frame ambient)
    (expected : List valtype) (values : List val)
    (empty : exec.frames.val=[]) (typed : ResultsTyped (Store.decodeStore view code store) expected values)
    (owned : Abs.Ownership.ValuesOwned (Store.ownershipBounds store) values)
    (words : ValuesAt exec.slots.val 0 values) :
    StructuredMachine.Execution
      view code store exec ⟨Store.decodeStore view code store,ambient,[],values⟩ expected 0 false ∧
    Abs.Ownership.StatefulOwned (Store.ownershipBounds store) ⟨Store.decodeStore view code store,ambient,[],values⟩ := by
  let certified := held.toCertifiedApiStore.toCertifiedSupportedStore
  constructor
  · refine ⟨rfl,?_,?_,typed,.empty empty,⟨rfl,rfl,words⟩⟩
    · refine ⟨⟨held.well_formed,certified.functions_typed,ambientWf,.nil _,Spec.resultsTyped_wf typed,?_,?_⟩,
        certified.contents_typed⟩
      · simp
      · simp [Forall]
    · exact ⟨by simp [Forall],certified.supported⟩
  · exact ⟨⟨owned,by simp⟩,held.shape.stateful_heap_owned code⟩
end Exec.Theorems.OpenReentrantControl
