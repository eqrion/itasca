import Exec.Spec.Typing.StoreTypingExtension

/-! Store typing after point mutations follows from independently typed changed
objects, extension of old objects, and exact address-space updates. -/

namespace Exec.Spec
open SpecExt

theorem source_store_of_component_members {s t : store} (typed : Store_ok s) (extension : Extend_store s t)
    (globals : Forall (fun object => object ∈ s.GLOBALS ∨ Globalinst_ok t object object.TYPE) t.GLOBALS)
    (memories : Forall (fun object => object ∈ s.MEMS ∨ Meminst_ok t object object.TYPE) t.MEMS)
    (tables : Forall (fun object => object ∈ s.TABLES ∨ Tableinst_ok t object object.TYPE) t.TABLES)
    (functions : Forall (fun object => object ∈ s.FUNCS ∨ Funcinst_ok t object object.TYPE) t.FUNCS)
    (data : Forall (fun object => object ∈ s.DATAS ∨ Datainst_ok t object .OK) t.DATAS)
    (elements : Forall (fun object => object ∈ s.ELEMS ∨ Eleminst_ok t object object.TYPE) t.ELEMS) : Store_ok t := by
  have components := source_store_components typed
  apply source_store_of_components ?_ (extend_store_wf extension).2
  constructor
  · intro object member
    rcases globals object member with old | fresh
    · exact globalinst_typing_extend extension (components.globals object old)
    · exact fresh
  · intro object member
    rcases memories object member with old | fresh
    · exact meminst_typing_extend extension (components.memories object old)
    · exact fresh
  · intro object member
    rcases tables object member with old | fresh
    · exact tableinst_typing_extend extension (components.tables object old)
    · exact fresh
  · intro object member
    rcases functions object member with old | fresh
    · exact funcinst_typing_extend extension (components.functions object old)
    · exact fresh
  · intro object member
    rcases data object member with old | fresh
    · exact datainst_typing_extend extension (components.data object old)
    · exact fresh
  · intro object member
    rcases elements object member with old | fresh
    · exact eleminst_typing_extend extension (components.elements object old)
    · exact fresh

theorem list_modify_as_set {A : Type} [Inhabited A] (xs : List A) (index : Nat) (update : A → A) :
    xs.modify index update=xs.set index (update xs[index]!) := by
  simpa only [List.getElem!_eq_getElem?_getD] using List.modify_eq_set update index xs

theorem list_mem_set_cases {A : Type} {xs : List A} {index : Nat} {value object : A}
    (member : object ∈ xs.set index value) : object ∈ xs ∨ object=value := by
  induction xs generalizing index with
  | nil => simp at member
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [List.set,List.mem_cons] at member
      rcases member with rfl | member
      · exact Or.inr rfl
      · exact Or.inl (by simp [member])
    | succ index =>
      simp only [List.set,List.mem_cons] at member
      rcases member with rfl | member
      · exact Or.inl (by simp)
      · rcases ih member with old | same
        · exact Or.inl (by simp [old])
        · exact Or.inr same

theorem list_set_members {A : Type} {property : A → Prop} (xs : List A) (index : Nat) (value : A)
    (typed : property value) : Forall (fun object => object ∈ xs ∨ property object) (xs.set index value) := by
  intro object member
  rcases list_mem_set_cases member with old | rfl
  · exact Or.inl old
  · exact Or.inr typed

theorem source_store_global_set {s t : store} (typed : Store_ok s) (extension : Extend_store s t)
    (index : Nat) (value : globalinst) (same : t={s with GLOBALS := s.GLOBALS.set index value})
    (fresh : Globalinst_ok t value value.TYPE) : Store_ok t := by
  cases same
  apply source_store_of_component_members typed extension
  · exact list_set_members _ _ _ fresh
  all_goals intro object member; exact Or.inl member

theorem source_store_memory_set {s t : store} (typed : Store_ok s) (extension : Extend_store s t)
    (index : Nat) (value : meminst) (same : t={s with MEMS := s.MEMS.set index value})
    (fresh : Meminst_ok t value value.TYPE) : Store_ok t := by
  cases same
  apply source_store_of_component_members typed extension
  · intro object member; exact Or.inl member
  · exact list_set_members _ _ _ fresh
  all_goals intro object member; exact Or.inl member

theorem source_store_table_set {s t : store} (typed : Store_ok s) (extension : Extend_store s t)
    (index : Nat) (value : tableinst) (same : t={s with TABLES := s.TABLES.set index value})
    (fresh : Tableinst_ok t value value.TYPE) : Store_ok t := by
  cases same
  apply source_store_of_component_members typed extension
  · intro object member; exact Or.inl member
  · intro object member; exact Or.inl member
  · exact list_set_members _ _ _ fresh
  all_goals intro object member; exact Or.inl member

theorem source_store_data_set {s t : store} (typed : Store_ok s) (extension : Extend_store s t)
    (index : Nat) (value : datainst) (same : t={s with DATAS := s.DATAS.set index value})
    (fresh : Datainst_ok t value .OK) : Store_ok t := by
  cases same
  apply source_store_of_component_members typed extension
  · intro object member; exact Or.inl member
  · intro object member; exact Or.inl member
  · intro object member; exact Or.inl member
  · intro object member; exact Or.inl member
  · exact list_set_members _ _ _ fresh
  · intro object member; exact Or.inl member

theorem source_store_element_set {s t : store} (typed : Store_ok s) (extension : Extend_store s t)
    (index : Nat) (value : eleminst) (same : t={s with ELEMS := s.ELEMS.set index value})
    (fresh : Eleminst_ok t value value.TYPE) : Store_ok t := by
  cases same
  apply source_store_of_component_members typed extension
  · intro object member; exact Or.inl member
  · intro object member; exact Or.inl member
  · intro object member; exact Or.inl member
  · intro object member; exact Or.inl member
  · intro object member; exact Or.inl member
  · exact list_set_members _ _ _ fresh

end Exec.Spec
