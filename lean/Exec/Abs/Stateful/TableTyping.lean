import Exec.Abs.Stateful.Continuation
import Exec.Abs.Core.MemoryTyping
namespace Exec.Abs.Stateful
open SpecExt Exec.Spec

def tableElementType : tabletype → reftype
  | .mk_tabletype _ type => type

theorem extern_table_lookup {s : store} {address : Nat} {type : tabletype}
    (typed : Externaddr_ok s (.TABLE address) (.TABLE type)) :
    ∃ object, s.TABLES[address]? = some object ∧ tableElementType object.TYPE = tableElementType type := by
  generalize addressEq : externaddr.TABLE address = external at typed
  generalize typeEq : externtype.TABLE type = externalType at typed
  induction typed generalizing type with
  | table a object bound found wf ext =>
    cases addressEq
    cases typeEq
    refine ⟨object,?_,rfl⟩
    simpa [getElem!_pos,bound] using congrArg some found
  | sub external old new typed sub wf oldWf newWf ih =>
    cases sub with
    | table old new relation _ _ =>
      cases typeEq
      cases relation with
      | mk_Tabletype_sub old type new _ _ _ =>
        obtain ⟨object,found,same⟩ := ih (type := .mk_tabletype old type) addressEq rfl
        exact ⟨object,found,same⟩
    | _ => cases typeEq
  | _ => cases addressEq

theorem table_lookup {s : store} {module : moduleinst} {C : context}
    (bindings : ModuleBindings s module C) {index : Nat} {type : tabletype}
    (found : C.TABLES[index]? = some type) :
    ∃ address object, module.TABLES[index]? = some address ∧
      s.TABLES[address]? = some object ∧ tableElementType object.TYPE = tableElementType type := by
  have right := (List.getElem?_eq_some_iff.mp found).1
  have left : index < module.TABLES.length := by rw [bindings.tables.length_eq]; exact right
  have relation := bindings.tables.get left right
  have value := (List.getElem?_eq_some_iff.mp found).2
  simp only [List.get_eq_getElem,value] at relation
  obtain ⟨object,lookup,objectType⟩ := extern_table_lookup relation
  exact ⟨module.TABLES[index],object,List.getElem?_eq_getElem left,lookup,objectType⟩

theorem table_references {s : store} (contents : StoreContentsTyped s) {object : tableinst}
    (member : object ∈ s.TABLES) : Forall (fun value => Ref_ok s value (tableElementType object.TYPE)) object.REFS := by
  have typed := contents.tables object member
  cases typed with
  | mk_Tableinst_ok count maximum type refs typeOk refsOk length _ wf typeWf => exact refsOk

private def minimum : limits → Nat
  | .mk_limits (.mk_uN count) _ => count

private theorem limits_minimum {type : limits} {bound : Nat} (typed : Limits_ok type bound) :
    minimum type ≤ bound := by cases typed; assumption

theorem table_size_bound {s : store} (contents : StoreContentsTyped s) {object : tableinst}
    (member : object ∈ s.TABLES) : object.REFS.length < 2^32 := by
  have typed := contents.tables object member
  cases typed with
  | mk_Tableinst_ok count maximum type refs typeOk refsOk length _ wf typeWf =>
    dsimp only
    rw [length]
    cases typeOk with
    | mk_Tabletype_ok _ _ limits _ =>
      have bound := limits_minimum limits
      change count ≤ _ at bound
      norm_num at bound ⊢
      omega

theorem memory_pages_bound {s : store} (contents : StoreContentsTyped s) {object : meminst}
    (member : object ∈ s.MEMS) : object.BYTES.length / 65536 ≤ 65536 := by
  have typed := contents.memories object member
  cases typed with
  | mk_Meminst_ok count maximum bytes typeOk length _ wf typeWf =>
    dsimp only
    rw [length]
    simp only [Ki]
    norm_num
    cases typeOk with
    | mk_Memtype_ok _ limits _ =>
      have bound := limits_minimum limits
      change count ≤ _ at bound
      norm_num at bound
      exact bound

end Exec.Abs.Stateful
