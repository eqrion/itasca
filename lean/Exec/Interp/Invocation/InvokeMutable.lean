import Exec.Interp.Invocation.InvokeMutableCauses
namespace Exec.Interp
open Aeneas Aeneas.Std

theorem invoke_with_mutable_resource_composition_mode {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allowDivergence : Bool)
    (allocation : Platform.AllocCorrect allocator)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst)
    (signature : Itasca.types.FuncType) (args : Slice runtime.Value)
    (results : alloc.vec.Vec runtime.Value)
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ()))
    (owned : ∀ value ∈ args.val, ValueOwnedFits store.id value)
    (entry : runtime.interp.Execution → Prop)
    (retained : runtime.store.Store M → Prop) (initial : retained store)
    (property : runtime.store.Store M → List val → Prop)
    (errorProperty : runtime.store.Store M → runtime.ExecError → Prop)
    (resourceError : ∀ after reason, (reason = .Values ∨ reason = .Allocation) → errorProperty after (.Exhausted reason))
    (called : ∀ prepared p, prepared.store = store.id → prepared.frames.val = [] →
      ValuesAt prepared.slots.val 0 (args.val.map sourceValue) →
      runtime.interp.call memory hooks floats allocator prepared store p address 0#usize ⦃ out =>
        out.2.2.1 = store ∧ (out.1 = .Ok () → entry out.2.1) ∧
          (∀ error, out.1 = .Err error → errorProperty store error) ⦄)
    (executed : ∀ prepared p, entry prepared →
      InvocationWP allowDivergence
        (runtime.interp.invoke_with_loop1 memory hooks floats allocator prepared store p (.Ok ()))
        (fun (_, words, _, _, _, afterStore, _, status) =>
          afterStore.id = store.id ∧ afterStore.funcs = store.funcs ∧ afterStore.types = store.types ∧ retained afterStore ∧
          (status = .Ok () → ∃ values,
            signature.results.val.map sourceType = values.map Code.valueType ∧
            (∀ value ∈ values, wf_val value) ∧
            (∀ value ∈ values, ResultIndexFits value) ∧
            ValuesAt words.val 0 values ∧ property afterStore values) ∧
          (∀ error, status = .Err error → errorProperty afterStore error))) :
    InvocationWP allowDivergence
      (runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results)
      (fun out => retained out.2.2.1 ∧ (out.1 = .Ok () → property out.2.2.1 (out.2.2.2.2.val.map sourceValue)) ∧
        (∀ error, out.1 = .Err error → errorProperty out.2.2.1 error)) := by
  apply invoke_with_mutable_causes_composition_mode memory hooks floats allocator allowDivergence allocation
    exec store platform address function signature args results owner hf hs accepted owned entry retained initial
    property errorProperty
  · intro after error cause
    rcases cause.kind with rfl | rfl
    · exact resourceError after _ (Or.inl rfl)
    · exact resourceError after _ (Or.inr rfl)
  · exact called
  · exact executed

theorem invoke_with_mutable_error_composition_mode {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allowDivergence : Bool)
    (allocation : Platform.AllocCorrect allocator)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst)
    (signature : Itasca.types.FuncType) (args : Slice runtime.Value)
    (results : alloc.vec.Vec runtime.Value)
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ()))
    (owned : ∀ value ∈ args.val, ValueOwnedFits store.id value)
    (entry : runtime.interp.Execution → Prop)
    (retained : runtime.store.Store M → Prop) (initial : retained store)
    (property : runtime.store.Store M → List val → Prop)
    (errorProperty : runtime.store.Store M → runtime.ExecError → Prop)
    (resourceError : ∀ after reason, errorProperty after (.Exhausted reason))
    (called : ∀ prepared p, prepared.store = store.id → prepared.frames.val = [] →
      ValuesAt prepared.slots.val 0 (args.val.map sourceValue) →
      runtime.interp.call memory hooks floats allocator prepared store p address 0#usize ⦃ out =>
        out.2.2.1 = store ∧ (out.1 = .Ok () → entry out.2.1) ∧
          (∀ error, out.1 = .Err error → errorProperty store error) ⦄)
    (executed : ∀ prepared p, entry prepared →
      InvocationWP allowDivergence
        (runtime.interp.invoke_with_loop1 memory hooks floats allocator prepared store p (.Ok ()))
        (fun (_, words, _, _, _, afterStore, _, status) =>
          afterStore.id = store.id ∧ afterStore.funcs = store.funcs ∧ afterStore.types = store.types ∧ retained afterStore ∧
          (status = .Ok () → ∃ values,
            signature.results.val.map sourceType = values.map Code.valueType ∧
            (∀ value ∈ values, wf_val value) ∧
            (∀ value ∈ values, ResultIndexFits value) ∧
            ValuesAt words.val 0 values ∧ property afterStore values) ∧
          (∀ error, status = .Err error → errorProperty afterStore error))) :
    InvocationWP allowDivergence
      (runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results)
      (fun out => retained out.2.2.1 ∧ (out.1 = .Ok () → property out.2.2.1 (out.2.2.2.2.val.map sourceValue)) ∧
        (∀ error, out.1 = .Err error → errorProperty out.2.2.1 error)) := by
  exact invoke_with_mutable_resource_composition_mode memory hooks floats allocator allowDivergence allocation
    exec store platform address function signature args results owner hf hs accepted owned entry retained initial
    property errorProperty (fun after reason _ => resourceError after reason) called executed

theorem invoke_with_mutable_error_composition {M P F A : Type}
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
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ()))
    (owned : ∀ value ∈ args.val, ValueOwnedFits store.id value)
    (entry : runtime.interp.Execution → Prop)
    (retained : runtime.store.Store M → Prop) (initial : retained store)
    (property : runtime.store.Store M → List val → Prop)
    (errorProperty : runtime.store.Store M → runtime.ExecError → Prop)
    (resourceError : ∀ after reason, errorProperty after (.Exhausted reason))
    (called : ∀ prepared p, prepared.store = store.id → prepared.frames.val = [] →
      ValuesAt prepared.slots.val 0 (args.val.map sourceValue) →
      runtime.interp.call memory hooks floats allocator prepared store p address 0#usize ⦃ out =>
        out.2.2.1 = store ∧ (out.1 = .Ok () → entry out.2.1) ∧
          (∀ error, out.1 = .Err error → errorProperty store error) ⦄)
    (executed : ∀ prepared p, entry prepared →
      WP.dspec
        (runtime.interp.invoke_with_loop1 memory hooks floats allocator prepared store p (.Ok ()))
        (fun (_, words, _, _, _, afterStore, _, status) =>
          afterStore.id = store.id ∧ afterStore.funcs = store.funcs ∧ afterStore.types = store.types ∧ retained afterStore ∧
          (status = .Ok () → ∃ values,
            signature.results.val.map sourceType = values.map Code.valueType ∧
            (∀ value ∈ values, wf_val value) ∧
            (∀ value ∈ values, ResultIndexFits value) ∧
            ValuesAt words.val 0 values ∧ property afterStore values) ∧
          (∀ error, status = .Err error → errorProperty afterStore error))) :
    WP.dspec
      (runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results)
      (fun out => retained out.2.2.1 ∧ (out.1 = .Ok () → property out.2.2.1 (out.2.2.2.2.val.map sourceValue)) ∧
        (∀ error, out.1 = .Err error → errorProperty out.2.2.1 error)) := by
  exact invoke_with_mutable_error_composition_mode memory hooks floats allocator true allocation exec store platform address function signature args results owner hf hs accepted owned entry retained initial property errorProperty resourceError called executed

theorem invoke_with_mutable_resource_composition {M P F A : Type}
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
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ()))
    (owned : ∀ value ∈ args.val, ValueOwnedFits store.id value)
    (entry : runtime.interp.Execution → Prop)
    (retained : runtime.store.Store M → Prop) (initial : retained store)
    (property : runtime.store.Store M → List val → Prop)
    (errorProperty : runtime.store.Store M → runtime.ExecError → Prop)
    (resourceError : ∀ after reason, (reason = .Values ∨ reason = .Allocation) → errorProperty after (.Exhausted reason))
    (called : ∀ prepared p, prepared.store = store.id → prepared.frames.val = [] →
      ValuesAt prepared.slots.val 0 (args.val.map sourceValue) →
      runtime.interp.call memory hooks floats allocator prepared store p address 0#usize ⦃ out =>
        out.2.2.1 = store ∧ (out.1 = .Ok () → entry out.2.1) ∧
          (∀ error, out.1 = .Err error → errorProperty store error) ⦄)
    (executed : ∀ prepared p, entry prepared →
      WP.dspec
        (runtime.interp.invoke_with_loop1 memory hooks floats allocator prepared store p (.Ok ()))
        (fun (_, words, _, _, _, afterStore, _, status) =>
          afterStore.id = store.id ∧ afterStore.funcs = store.funcs ∧ afterStore.types = store.types ∧ retained afterStore ∧
          (status = .Ok () → ∃ values,
            signature.results.val.map sourceType = values.map Code.valueType ∧
            (∀ value ∈ values, wf_val value) ∧
            (∀ value ∈ values, ResultIndexFits value) ∧
            ValuesAt words.val 0 values ∧ property afterStore values) ∧
          (∀ error, status = .Err error → errorProperty afterStore error))) :
    WP.dspec
      (runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results)
      (fun out => retained out.2.2.1 ∧ (out.1 = .Ok () → property out.2.2.1 (out.2.2.2.2.val.map sourceValue)) ∧
        (∀ error, out.1 = .Err error → errorProperty out.2.2.1 error)) := by
  exact invoke_with_mutable_resource_composition_mode memory hooks floats allocator true allocation exec store platform address function signature args results owner hf hs accepted owned entry retained initial property errorProperty resourceError called executed

end Exec.Interp
