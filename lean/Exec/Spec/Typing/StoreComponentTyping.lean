import Exec.Spec.Typing.FrameEnvironment

/-! Canonical component typing is equivalent to the generated store judgment
when store well-formedness is retained. External lookups preserve payload types. -/

namespace Exec.Spec
open SpecExt

private theorem paired_left {A B : Type} {relation : A → B → Prop} {xs : List A} {ys : List B}
    (paired : List.Forall₂ relation xs ys) {x : A} (member : x ∈ xs) : ∃ y, relation x y := by
  obtain ⟨index,bound,rfl⟩ := List.mem_iff_getElem.mp member
  have other : index<ys.length := by rw [← paired.length_eq]; exact bound
  exact ⟨ys[index],paired.get bound other⟩

private theorem typed_members {A B : Type} {relation : A → B → Prop} {property : A → Prop}
    {xs : List A} {ys : List B} (paired : List.Forall₂ relation xs ys)
    (implies : ∀ x y, relation x y → property x) : Forall property xs := by
  intro x member
  obtain ⟨y,typed⟩ := paired_left paired member
  exact implies x y typed

structure SourceStoreComponents (s : store) : Prop where
  globals : Forall (fun global => Globalinst_ok s global global.TYPE) s.GLOBALS
  memories : Forall (fun memory => Meminst_ok s memory memory.TYPE) s.MEMS
  tables : Forall (fun table => Tableinst_ok s table table.TYPE) s.TABLES
  functions : Forall (fun fn => Funcinst_ok s fn fn.TYPE) s.FUNCS
  data : Forall (fun entry => Datainst_ok s entry .OK) s.DATAS
  elements : Forall (fun entry => Eleminst_ok s entry entry.TYPE) s.ELEMS

theorem source_store_components {s : store} (typed : Store_ok s) : SourceStoreComponents s := by
  cases typed with
  | mk_Store_ok globals globalTypes mems memTypes tables tableTypes funcs funcTypes datas dataTypes elems elemTypes
      glength globalsOk mlength memsOk tlength tablesOk flength funcsOk dlength datasOk elength elemsOk
      storeEq storeWf memTypesWf tableTypesWf recordWf =>
    cases storeEq
    let current : store := ⟨funcs,globals,tables,mems,elems,datas⟩
    constructor
    · refine typed_members (property := fun global => Globalinst_ok current global global.TYPE) (forall₂_of_lengths glength globalsOk) ?_
      intro global type valid
      cases valid
      constructor <;> assumption
    · refine typed_members (property := fun memory => Meminst_ok current memory memory.TYPE) (forall₂_of_lengths mlength memsOk) ?_
      intro memory type valid
      cases valid
      constructor <;> assumption
    · refine typed_members (property := fun table => Tableinst_ok current table table.TYPE) (forall₂_of_lengths tlength tablesOk) ?_
      intro table type valid
      cases valid
      constructor <;> assumption
    · refine typed_members (property := fun fn => Funcinst_ok current fn fn.TYPE) (forall₂_of_lengths flength funcsOk) ?_
      intro fn type valid
      cases valid <;> constructor <;> assumption
    · refine typed_members (property := fun entry => Datainst_ok current entry .OK) (forall₂_of_lengths dlength datasOk) ?_
      intro entry type valid
      cases valid
      constructor <;> assumption
    · refine typed_members (property := fun entry => Eleminst_ok current entry entry.TYPE) (forall₂_of_lengths elength elemsOk) ?_
      intro entry type valid
      cases valid
      constructor <;> assumption

theorem source_store_of_components {s : store} (components : SourceStoreComponents s)
    (storeWf : wf_store s) : Store_ok s := by
  apply Store_ok.mk_Store_ok s s.GLOBALS (s.GLOBALS.map globalinst.TYPE)
    s.MEMS (s.MEMS.map meminst.TYPE) s.TABLES (s.TABLES.map tableinst.TYPE)
    s.FUNCS (s.FUNCS.map funcinst.TYPE) s.DATAS (s.DATAS.map (fun _ => datatype.OK))
    s.ELEMS (s.ELEMS.map eleminst.TYPE)
  · simp
  · exact fun _ member => List.forall₂_zip
      (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr components.globals)) member
  · simp
  · exact fun _ member => List.forall₂_zip
      (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr components.memories)) member
  · simp
  · exact fun _ member => List.forall₂_zip
      (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr components.tables)) member
  · simp
  · exact fun _ member => List.forall₂_zip
      (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr components.functions)) member
  · simp
  · exact fun _ member => List.forall₂_zip
      (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr components.data)) member
  · simp
  · exact fun _ member => List.forall₂_zip
      (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr components.elements)) member
  · rfl
  · exact storeWf
  · intro type member
    obtain ⟨memory,present,rfl⟩ := List.mem_map.mp member
    cases components.memories memory present <;> assumption
  · intro type member
    obtain ⟨table,present,rfl⟩ := List.mem_map.mp member
    cases components.tables table present <;> assumption
  · exact storeWf

theorem external_global_lookup {s : store} {address : Nat} {type : globaltype}
    (typed : Externaddr_ok s (.GLOBAL address) (.GLOBAL type)) :
    ∃ object, s.GLOBALS[address]?=some object ∧ object.TYPE=type := by
  generalize addressEq : externaddr.GLOBAL address=external at typed
  generalize typeEq : externtype.GLOBAL type=externalType at typed
  induction typed with
  | global a object bound found _ _ =>
    cases addressEq
    cases typeEq
    refine ⟨object,?_,rfl⟩
    simpa [getElem!_pos,bound] using congrArg some found
  | sub external old new typed sub _ _ _ ih =>
    cases sub with
    | global old new same _ _ =>
      cases same
      exact ih addressEq typeEq
    | _ => cases typeEq
  | _ => cases addressEq

def sourceTableElementType : tabletype → reftype
  | .mk_tabletype _ type => type

theorem external_table_lookup {s : store} {address : Nat} {type : tabletype}
    (typed : Externaddr_ok s (.TABLE address) (.TABLE type)) :
    ∃ object, s.TABLES[address]?=some object ∧ sourceTableElementType object.TYPE=sourceTableElementType type := by
  generalize addressEq : externaddr.TABLE address=external at typed
  generalize typeEq : externtype.TABLE type=externalType at typed
  induction typed generalizing type with
  | table a object bound found _ _ =>
    cases addressEq
    cases typeEq
    refine ⟨object,?_,rfl⟩
    simpa [getElem!_pos,bound] using congrArg some found
  | sub external old new typed sub _ _ _ ih =>
    cases sub with
    | table old new relation _ _ =>
      cases typeEq
      cases relation with
      | mk_Tabletype_sub old type new _ _ _ =>
        obtain ⟨object,found,same⟩ := ih (type := .mk_tabletype old type) addressEq rfl
        exact ⟨object,found,same⟩
    | _ => cases typeEq
  | _ => cases addressEq

end Exec.Spec
