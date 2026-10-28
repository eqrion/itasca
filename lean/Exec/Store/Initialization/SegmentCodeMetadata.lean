import Exec.Store.Initialization.SegmentReady
import Exec.Store.Invariant.InstantiationCode

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Initialization bulk operations retain every function and signature lookup
used by an installed compiler certificate. -/
theorem SegmentAddressSpace.function_table {M : Type} {before after : runtime.store.Store M}
    (metadata : SegmentAddressSpace before after) {inst : runtime.store.ModuleInst} {types : List functype}
    (table : Interp.FunctionTable before inst types) : Interp.FunctionTable after inst types := by
  simpa only [Interp.FunctionTable, metadata.identity, metadata.functions, metadata.signatures] using table

/-- Source start validation and the constructed instance function table resolve
the start function to an owned actual function with no parameters or results. -/
theorem start_function_resolves {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst}
    (table : Interp.FunctionTable store inst (inst.module.module.env.func_types.val.map decodeFuncType))
    (valid : Itasca.ModuleEnv.Valid inst.module.module.env inst.module.profile)
    (index : U32) (start : inst.module.module.env.start = some index) :
    ∃ address function signature, inst.funcs.val[index.val]? = some address ∧
      address.store = store.id ∧ store.funcs.val[address.index.val]? = some function ∧
      store.types.val[function.signature.val]? = some signature ∧
      signature.params.val = [] ∧ signature.results.val = [] := by
  obtain ⟨bound, params, results⟩ := valid.start index start
  have rawFound := List.getElem?_eq_getElem bound
  have decodedFound : (inst.module.module.env.func_types.val.map decodeFuncType)[index.val]? =
      some (decodeFuncType inst.module.module.env.func_types.val[index.val]) := by
    simp only [List.getElem?_map, rawFound, Option.map_some]
  obtain ⟨address, function, signature, mapped, owned, found, typed, decoded⟩ := table.resolve index.val _ decodedFound
  have decodedEmpty : decodeFuncType signature = .mk_functype (.mk_list []) (.mk_list []) := by
    simpa only [decodeFuncType, params, results, List.map_nil] using decoded
  have empty : signature.params.val = [] ∧ signature.results.val = [] := by
    simpa only [decodeFuncType, functype.mk_functype.injEq, list.mk_list.injEq,
      List.map_eq_nil_iff] using decodedEmpty
  exact ⟨address, function, signature, mapped, owned, found, typed, empty⟩

end Itasca.Runtime.Store
