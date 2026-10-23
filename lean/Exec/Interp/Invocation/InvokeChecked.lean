import Exec.Interp.Invocation.InvokeCompose

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- The public checker rejects mismatched argument signatures before entry;
accepted arguments use the separately proved call and loop contracts. -/
theorem invoke_with_checked_composition {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst)
    (signature : Itasca.types.FuncType) (args : Slice runtime.Value)
    (results : alloc.vec.Vec runtime.Value)
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (owned : ∀ value ∈ args.val, ValueOwnedFits store.id value)
    (entry : runtime.interp.Execution → Prop) (property : List val → Prop)
    (called : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ()) →
      ∀ prepared p, prepared.store = store.id → prepared.frames.val = [] →
      ValuesAt prepared.slots.val 0 (args.val.map sourceValue) →
      runtime.interp.call memory hooks floats allocator prepared store p address 0#usize ⦃ out =>
        out.2.2.1 = store ∧ (out.1 = .Ok () → entry out.2.1) ⦄)
    (executed : ∀ prepared p, entry prepared →
      runtime.interp.invoke_with_loop1 memory hooks floats allocator prepared store p (.Ok ())
        ⦃ (_, words, _, _, _, afterStore, _, status) => afterStore = store ∧
          (status = .Ok () → ∃ values,
            signature.results.val.map sourceType = values.map Code.valueType ∧
            (∀ value ∈ values, wf_val value) ∧
            (∀ value ∈ values, ResultIndexFits value) ∧
            ValuesAt words.val 0 values ∧ property values) ⦄div) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => out.2.2.1 = store ∧ (out.1 = .Ok () → property (out.2.2.2.2.val.map sourceValue)) ⦄div := by
  obtain ⟨answer, checked, decision⟩ := WP.spec_imp_exists
    (check_values_effect memory store args (alloc.vec.Vec.deref signature.params))
  cases answer with
  | Ok unit =>
    cases unit
    exact invoke_with_composition memory hooks floats allocator allocation exec store platform address
      function signature args results owner hf hs checked owned entry property (called checked) executed
  | Err error =>
    obtain ⟨found, lookup, same⟩ := WP.spec_imp_exists
      (func_type_lookup memory store address function signature owner hf hs)
    subst found
    simp [runtime.interp.invoke_with, lookup, checked, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end Exec.Interp
