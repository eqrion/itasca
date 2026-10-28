import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Existing frame metadata survives object creation when old entries retain
exact raw identities and indices. Payload mutation is unrestricted here. This
is a transport relation, not an assumed law of arbitrary host callbacks. -/
structure FrameStorePrefix {M : Type} (before after : runtime.store.Store M) : Prop where
  identity : after.id = before.id
  functions : after.funcs.val.take before.funcs.length = before.funcs.val
  types : after.types.val.take before.types.length = before.types.val
  instances : after.instances.val.take before.instances.length = before.instances.val

/-- Every retained module type index was already present before extension. -/
def FrameTypeBounds {M : Type} (store : runtime.store.Store M) : Prop :=
  ∀ inst ∈ store.instances.val, ∀ index ∈ inst.types.val, index.val < store.types.length

private theorem retained_lookup {T : Type} {before after : List T}
    (retained : after.take before.length = before) {index : Nat} {value : T}
    (found : before[index]? = some value) : after[index]? = some value := by
  have bound := (List.getElem?_eq_some_iff.mp found).1
  have same := congrArg (fun xs => xs[index]?) retained
  simpa only [List.getElem?_take,if_pos bound,found] using same

theorem FrameStorePrefix.refl {M : Type} (store : runtime.store.Store M) :
    FrameStorePrefix store store := by
  exact ⟨rfl,List.take_length,List.take_length,List.take_length⟩

private theorem retained_trans {T : Type} {a b c : List T}
    (first : b.take a.length = a) (second : c.take b.length = b) : c.take a.length = a := by
  have bound : a.length ≤ b.length := by
    have lengths := congrArg List.length first
    simp only [List.length_take] at lengths
    omega
  calc
    c.take a.length = (c.take b.length).take a.length := by simp only [List.take_take,Nat.min_eq_left bound]
    _ = b.take a.length := by rw [second]
    _ = a := first

theorem FrameStorePrefix.trans {M : Type} {a b c : runtime.store.Store M}
    (first : FrameStorePrefix a b) (second : FrameStorePrefix b c) : FrameStorePrefix a c :=
  ⟨second.identity.trans first.identity,retained_trans first.functions second.functions,
    retained_trans first.types second.types,retained_trans first.instances second.instances⟩

theorem FrameStoreMetadata.prefix {M : Type} {before after : runtime.store.Store M}
    (same : FrameStoreMetadata before after) : FrameStorePrefix before after := by
  exact ⟨same.identity,by simp [same.functions],by simp [same.types],by simp [same.instances]⟩

theorem FrameStorePrefix.function_lookup {M : Type} {before after : runtime.store.Store M}
    (retained : FrameStorePrefix before after) {index : Nat} {function : runtime.store.FuncInst}
    (found : before.funcs.val[index]? = some function) : after.funcs.val[index]? = some function :=
  retained_lookup retained.functions found

theorem FrameStorePrefix.type_lookup {M : Type} {before after : runtime.store.Store M}
    (retained : FrameStorePrefix before after) {index : Nat} {signature : Itasca.types.FuncType}
    (found : before.types.val[index]? = some signature) : after.types.val[index]? = some signature :=
  retained_lookup retained.types found

theorem FrameStorePrefix.instance_lookup {M : Type} {before after : runtime.store.Store M}
    (retained : FrameStorePrefix before after) {index : Nat} {inst : runtime.store.ModuleInst}
    (found : before.instances.val[index]? = some inst) : after.instances.val[index]? = some inst :=
  retained_lookup retained.instances found

theorem FrameStorePrefix.decodeInstance {M : Type} {before after : runtime.store.Store M}
    (retained : FrameStorePrefix before after) (inst : runtime.store.ModuleInst)
    (typeBounds : ∀ index ∈ inst.types.val, index.val < before.types.length) :
    Store.decodeInstance after inst = Store.decodeInstance before inst := by
  unfold Store.decodeInstance
  congr 1
  apply List.map_congr_left
  intro index member
  have bound := typeBounds index member
  have found : before.types.val[index.val]? = some before.types.val[index.val] := List.getElem?_eq_getElem bound
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map,found,retained.type_lookup found]

theorem FunctionTable.store_prefix {M : Type} {before after : runtime.store.Store M}
    (retained : FrameStorePrefix before after) {inst functions}
    (table : FunctionTable before inst functions) : FunctionTable after inst functions := by
  apply table.imp
  intro address ty entry
  obtain ⟨owner,function,signature,found,typed,decoded⟩ := entry
  exact ⟨owner.trans retained.identity.symm,function,signature,retained.function_lookup found,retained.type_lookup typed,decoded⟩

theorem FrameBinding.store_prefix {M : Type} {before after : runtime.store.Store M}
    (retained : FrameStorePrefix before after) (bounds : FrameTypeBounds before)
    {exec raw source} (binding : FrameBinding before exec raw source) : FrameBinding after exec raw source := by
  obtain ⟨inst,fn,compiled,signature,owner,member,found,functionAt,wasm,code,typed,moduleEq,results,locals,capacity⟩ := binding
  exact ⟨inst,fn,compiled,signature,owner.trans retained.identity.symm,member,retained.instance_lookup found,
    retained.function_lookup functionAt,wasm,code,retained.type_lookup typed,
    moduleEq.trans (retained.decodeInstance inst (bounds inst (List.mem_of_getElem? found))).symm,
    results,locals,capacity⟩

theorem FrameProgram.store_prefix {M : Type} {before after : runtime.store.Store M}
    (retained : FrameStorePrefix before after) {raw compiled locals results functions}
    (program : FrameProgram before raw compiled locals results functions) :
    FrameProgram after raw compiled locals results functions := by
  refine ⟨?_,program.checked,program.fetchBound,program.localSlots,program.epilogue⟩
  obtain ⟨inst,found,code,table⟩ := program.lookup
  exact ⟨inst,retained.instance_lookup found,code,table.store_prefix retained⟩

end Itasca.Runtime.Interp
