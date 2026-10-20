import Exec.Spec.Open.ExecutionReplies
import Exec.Store.Invariant.CheckedValuesComplete
import Exec.Theorems.Host.Open.Source.Control.Actions
import Exec.Theorems.Host.Chosen.HostChoiceMatching
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Native dynamic reply checking and independent source result checking agree
for store-owned callback results. Effects remain in the same reached store in
both accepted and rejected cases. -/
theorem checked_source_reply {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (store : runtime.store.Store M)
    (wellFormed : wf_store (Store.decodeStore view code store)) (signature : Itasca.types.FuncType)
    (values : alloc.vec.Vec runtime.Value) (status : HostStatus)
    (owned : ∀value∈values.val,Store.ValueInStore store value) :
    (checkedHostReply memory view code store signature values status).result=
      Spec.OpenExecution.checkedResult (Store.decodeStore view code store) (signature.results.val.map sourceType)
        (sourceReply status values.slice) := by
  classical
  have rawEq : values.slice.val=values.val := rfl
  cases status with
  | Err error=>simp [checkedHostReply,sourceReply,Spec.OpenExecution.checkedResult]
  | Ok unit=>
    cases unit
    obtain ⟨checked,actual,accepts⟩ := WP.spec_imp_exists (Store.check_values_source_iff memory view code store wellFormed
      values.slice signature.results owned)
    have deref : signature.results.deref=signature.results.slice := by
      apply Slice.ext
      simp only [alloc.vec.Vec.deref,Slice.from_val,alloc.vec.Vec.val]
    rw [deref] at actual
    simp only [rawEq] at accepts
    cases checked with
    | Ok unit=>
      cases unit
      have typed := accepts.mp rfl
      simp [checkedHostReply,sourceReply,Spec.OpenExecution.checkedResult,actual,rawEq,typed]
    | Err error=>
      have rejected : ¬ResultsTyped (Store.decodeStore view code store) (signature.results.val.map sourceType)
          (values.val.map sourceValue) := by
        intro typed
        have impossible := accepts.mpr typed
        cases impossible
      simp [checkedHostReply,sourceReply,Spec.OpenExecution.checkedResult,actual,rawEq,rejected]
end Exec.Theorems.OpenReentrantControl
