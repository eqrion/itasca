import Itasca.Runtime.Theorems.Api.InvocationCanonicalResources
import Itasca.Runtime.Interp.Relations.SourceCanonicalCapacity
import Itasca.Runtime.Interp.Relations.SourceAllocationCauses
import Itasca.Runtime.Interp.Invocation.InvokeMutableCauses
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

theorem InvocationResourceCause.canonical {M P A : Type}
    {allocator : runtime.platform.Alloc A} {hooks : runtime.platform.Platform P M}
    {exec : runtime.interp.Execution} {store : runtime.store.Store M}
    {signature : Itasca.types.FuncType} {results : alloc.vec.Vec runtime.Value}
    {error : runtime.ExecError} (initial : config) (sourceStore : _root_.store) (address : funcaddr)
    (cause : InvocationResourceCause allocator exec store signature results error) :
    CanonicalInvocationResourceCause allocator hooks initial sourceStore (Store.decodeFuncType signature) address
      store.limits.max_values.val store.limits.max_frames.val error := by
  rcases cause.kind with rfl | rfl
  · apply Or.inl
    simpa only [InvocationResourceCause,signatureWords,Store.decodeFuncType,typeSlots] using cause
  · apply Or.inl
    rcases cause with ⟨n,amount,refused⟩ | ⟨n,amount,refused⟩
    · exact Or.inl ⟨exec.slots,n,amount,refused⟩
    · exact Or.inr ⟨results,n,by simpa only [Store.decodeFuncType,List.length_map] using Nat.le_trans (Nat.le_of_eq amount) (Nat.sub_le _ _),refused⟩

theorem CallCause.invocation_canonical {M P A : Type}
    {allocator : runtime.platform.Alloc A} {hooks : runtime.platform.Platform P M}
    {prepared : runtime.interp.Execution} {store : runtime.store.Store M} {platform : P}
    {signature : Itasca.types.FuncType} {error : runtime.ExecError}
    (view : M → Slice U8) (code : Store.CodeInterpretation) (initial : config)
    (capacities : Store.FunctionCapacities code store) (typed : CoreFunctionsTyped view code store)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst) (instanceIndex functionIndex : Usize)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (hf : store.funcs.val[address.index.val]?=some function) (hw : function.code=.Wasm instanceIndex functionIndex)
    (hi : store.instances.val[instanceIndex.val]?=some inst) (hc : inst.module.functions.val[functionIndex.val]?=some compiled)
    (empty : prepared.frames.val=[])
    (cause : CallCause allocator hooks prepared store platform 0#usize compiled error) :
    CanonicalInvocationResourceCause allocator hooks initial (Store.decodeStore view code store)
      (Store.decodeFuncType signature) address.index.val store.limits.max_values.val store.limits.max_frames.val error := by
  cases error with
  | Terminated => exact ⟨platform,cause⟩
  | Exhausted reason =>
    cases reason with
    | CallStack =>
      apply Or.inl
      change store.limits.max_frames.val≤prepared.frames.length at cause
      have zero : prepared.frames.length=0 := by simp only [alloc.vec.Vec.length,empty,List.length_nil]
      have limit : store.limits.max_frames.val=0 := by omega
      simp [limit]
    | Values =>
      obtain ⟨words,capacity,bound⟩ := function_canonical_capacity_decoded view code store capacities typed
        address function instanceIndex functionIndex inst compiled hf hw hi hc
      change store.limits.max_values.val<(0#usize).val+compiled.slot_count.val at cause
      exact Or.inr (Or.inl ⟨words,capacity,by scalar_tac⟩)
    | Allocation =>
      obtain ⟨words,capacity,bound⟩ := function_canonical_capacity_decoded view code store capacities typed
        address function instanceIndex functionIndex inst compiled hf hw hi hc
      apply Or.inr; apply Or.inl; refine ⟨words,capacity,?_⟩
      rcases CallCause.source_allocation bound cause with ⟨n,amount,refused⟩ | refused
      · exact Or.inl ⟨prepared.slots,n,by simpa using amount,refused⟩
      · exact Or.inr ⟨prepared.frames,refused⟩
    | Objects => exact cause
  | _ => trivial
end Itasca.Runtime.Theorems
