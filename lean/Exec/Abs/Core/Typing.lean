import Exec.Abs.Core
import Exec.Abs.FrameTypingExtension

namespace Itasca.Runtime.Abs

/-- Semantic typing of store payloads used by mutable instructions. Function
bodies remain in `ATyped.functions`; no unproved generated `Store_ok` is used. -/
structure StoreContentsTyped (s : store) : Prop where
  globals : ∀ global ∈ s.GLOBALS, Globalinst_ok s global global.TYPE
  tables : ∀ table ∈ s.TABLES, Tableinst_ok s table table.TYPE
  memories : ∀ memory ∈ s.MEMS, Meminst_ok s memory memory.TYPE
  elements : ∀ element ∈ s.ELEMS, Eleminst_ok s element element.TYPE
  data : ∀ entry ∈ s.DATAS, Datainst_ok s entry .OK

structure CoreTyped (s : AState) : Prop where
  typed : ATyped s
  contents : StoreContentsTyped s.store

theorem extern_global_lookup {s : store} {address : Nat} {ty : globaltype}
    (typed : Externaddr_ok s (.GLOBAL address) (.GLOBAL ty)) :
    ∃ object, s.GLOBALS[address]? = some object ∧ object.TYPE = ty := by
  generalize he : externaddr.GLOBAL address = external at typed
  generalize ht : externtype.GLOBAL ty = externalType at typed
  induction typed with
  | global a object bound found wf ext =>
    cases he
    cases ht
    refine ⟨object,?_,rfl⟩
    simpa [getElem!_pos, bound] using congrArg some found
  | sub external old new typed sub wf oldWf newWf ih =>
    cases sub with
    | global old new same _ _ =>
      cases same
      exact ih he ht
    | _ => cases ht
  | _ => cases he

theorem ModuleBindings.global_lookup {s : store} {m : moduleinst} {C : context}
    (bindings : ModuleBindings s m C) {index : Nat} {ty : globaltype}
    (found : C.GLOBALS[index]? = some ty) :
    ∃ address object, m.GLOBALS[index]? = some address ∧
      s.GLOBALS[address]? = some object ∧ object.TYPE = ty := by
  have right := (List.getElem?_eq_some_iff.mp found).1
  have left : index < m.GLOBALS.length := by rw [bindings.globals.length_eq]; exact right
  have relation := bindings.globals.get left right
  have value : C.GLOBALS[index] = ty := (List.getElem?_eq_some_iff.mp found).2
  simp only [List.get_eq_getElem, value] at relation
  obtain ⟨object,lookup,objectType⟩ := extern_global_lookup relation
  exact ⟨m.GLOBALS[index],object,List.getElem?_eq_getElem left,lookup,objectType⟩

theorem StoreContentsTyped.global_value {s : store} (contents : StoreContentsTyped s)
    {address : Nat} {global : globalinst} {mutable : «mut»} {ty : valtype}
    (found : s.GLOBALS[address]? = some global)
    (type : global.TYPE = .mk_globaltype mutable ty) : Val_ok s global.VALUE ty := by
  have typed := contents.globals global (List.mem_of_getElem? found)
  cases typed with
  | mk_Globalinst_ok actual valueType value globalType valueTyped wf valueWf =>
    cases type
    exact valueTyped

end Itasca.Runtime.Abs
