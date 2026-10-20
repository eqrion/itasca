import Exec.Interp.Invocation.OpenInvoke
import Exec.Theorems.Api.ReadbackIssued
import Exec.Interp.Invocation.InvokePrefixCauses
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- Reading completed values cannot mutate the store or fabricate references.
Allocator refusal remains an ordinary API error, separate from source values. -/
theorem readback_values {M P A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (exec : runtime.interp.Execution) (token : P)
    (address : runtime.FuncAddr) (owner : address.store=store.id)
    (function : runtime.store.Function) (signature : Itasca.types.FuncType)
    (hf : store.funcs.val[address.index.val]?=some function)
    (hs : store.types.val[function.signature.val]?=some signature)
    (results : alloc.vec.Vec runtime.Value) (values : List val)
    (typed : ResultsTyped (Store.decodeStore view code store) (signature.results.val.map sourceType) values)
    (owned : Abs.Ownership.ValuesOwned (Store.ownershipBounds store) values)
    (words : ValuesAt exec.slots.val 0 values) :
    readback memory allocator address results (finishExecution (exec,store,token,.Ok ())) ⦃out=>
      out.2.1=exec ∧ out.2.2.1=store ∧ out.2.2.2.1=token ∧
      ((out.1=.Ok () ∧ out.2.2.2.2.val.map sourceValue=values ∧
        ∀value∈out.2.2.2.2.val,Store.ValueInStore store value) ∨
       (out.1=.Err (.Exhausted .Allocation) ∧ out.2.2.2.2=results ∧
         ∃n,allocator.reserve results n=.ok (false,results))) ⦄ := by
  unfold readback
  simp only [finishExecution,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with func_type_lookup memory store address function signature owner hf hs as ⟨found,same⟩
  subst found
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,lift]
  obtain ⟨decision,reserved⟩ := allocation.reserve_eq results
    (core.num.Usize.saturating_sub signature.results.len results.len)
  have reservation : runtime.reserve allocator results (core.num.Usize.saturating_sub signature.results.len results.len) =
      .ok ((if decision then .Ok () else .Err (.Exhausted .Allocation)),results) := by
    cases decision <;> simp [runtime.reserve,reserved]
  rw [reservation,bind_ok]
  cases decision with
  | false =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    exact ⟨_,reserved⟩
  | true =>
    simp only [ite_true,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step with clear_results results as ⟨cleared,empty⟩
    have tags : signature.results.val.map sourceType=values.map Code.valueType := by
      simpa only [show Code.valueType=Abs.valueType from funext valueType_eq_abs] using
        (Abs.results_type_of_typed typed).symm
    step with read_results_issued exec.slots store cleared signature.results values empty tags (Spec.resultsTyped_wf typed) owned words
      as ⟨after,returned,unchanged,same,issued⟩
    subst after
    try simp only [WP.spec_ok]
    exact ⟨trivial,Or.inl ⟨same,issued⟩⟩
end Exec.Theorems.OpenReentrantControl
