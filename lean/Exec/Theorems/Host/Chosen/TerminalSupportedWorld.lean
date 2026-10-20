import Exec.Theorems.Host.Chosen.TerminalExecutableWorld
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Root host resumption needs the checked supported store and source typing,
without requiring unrelated public instantiation ledgers in its continuation. -/
theorem terminal_supported_execution {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (certified : CertifiedSupportedStore Executable.emission Abs.ExecutableInstr view code store)
    (sourceTyped : Store_ok (Store.decodeStore view code store))
    (exec : runtime.interp.Execution) (ambient : frame) (ambientWf : wf_frame ambient)
    (expected : List valtype) (values : List val)
    (empty : exec.frames.val=[]) (typed : ResultsTyped (Store.decodeStore view code store) expected values)
    (owned : Abs.Ownership.ValuesOwned (Store.ownershipBounds store) values)
    (words : ValuesAt exec.slots.val 0 values) :
    StructuredMachine.Execution Executable.emission (Abs.SupportedState Abs.ExecutableInstr)
      view code store exec ⟨Store.decodeStore view code store,ambient,[],values⟩ expected 0 false ∧
    Abs.Ownership.StatefulOwned (Store.ownershipBounds store) ⟨Store.decodeStore view code store,ambient,[],values⟩ := by
  have sourceWf : wf_store (Store.decodeStore view code store) := by cases sourceTyped; assumption
  constructor
  · refine ⟨rfl,?_,?_,typed,.empty empty,⟨rfl,rfl,words⟩⟩
    · refine ⟨⟨sourceWf,certified.functions_typed,ambientWf,.nil _,Spec.resultsTyped_wf typed,?_,?_⟩,
        certified.contents_typed⟩
      · simp
      · simp [Forall]
    · exact ⟨by simp [Forall],certified.supported⟩
  · exact ⟨⟨owned,by simp⟩,certified.shape.stateful_heap_owned code⟩
end Exec.Theorems.OpenReentrantControl
