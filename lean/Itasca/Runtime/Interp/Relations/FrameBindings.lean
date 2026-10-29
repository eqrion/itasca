import Itasca.Runtime.Interp.Relations.Rel

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- The module bound to the active source frame is the decoded instance found
by the concrete frame's instance index. -/
theorem FrameBinding.module_lookup {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {raw : runtime.interp.Frame} {source : SourceMachine.AFrame}
    (binding : FrameBinding store exec raw source) (inst : runtime.store.ModuleInst)
    (lookup : store.instances.val[raw.instance.val]? = some inst) :
    source.module = Store.decodeInstance store inst := by
  obtain ⟨actual, fn, compiled, signature, _, _, found, _, _, _, _, moduleEq, _⟩ := binding
  have same : actual = inst := Option.some.inj (found.symm.trans lookup)
  exact same ▸ moduleEq

/-- Raw direct-call lookup and source CALL lookup use the identical retained
instance function map. -/
theorem FrameBinding.resolve_call {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {raw : runtime.interp.Frame} {source : SourceMachine.AFrame}
    (binding : FrameBinding store exec raw source) (inst : runtime.store.ModuleInst)
    (lookup : store.instances.val[raw.instance.val]? = some inst)
    (index : Nat) (address : runtime.FuncAddr)
    (found : inst.funcs.val[index]? = some address) :
    source.module.FUNCS[index]? = some address.index.val := by
  rw [binding.module_lookup inst lookup]
  simp only [Store.decodeInstance, List.getElem?_map, found, Option.map_some]

/-- A concrete defined-function entry selects precisely the retained source
body and owning module in the decoded store. -/
theorem defined_function_lookup {M : Type} (view : M → Slice U8)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst)
    (signature : Itasca.types.FuncType) (instanceIndex functionIndex : Usize)
    (inst : runtime.store.ModuleInst) (sourceCode : funccode)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (hw : function.code = .Wasm instanceIndex functionIndex)
    (hi : store.instances.val[instanceIndex.val]? = some inst)
    (hc : code instanceIndex.val inst.module functionIndex.val = sourceCode) :
    (Store.decodeStore view code store).FUNCS[address.index.val]? =
      some ⟨Store.decodeFuncType signature, Store.decodeInstance store inst, sourceCode⟩ := by
  simp [Store.decodeStore, Store.decodeFunction, List.getD_eq_getElem?_getD, hf, hs, hw, hi, hc]

end Itasca.Runtime.Interp
