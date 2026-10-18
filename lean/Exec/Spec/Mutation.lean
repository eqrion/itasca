import Exec.Spec.Extend

/-! Store allocation and mutation facts. Every endpoint retains the generated
well-formedness premise; these facts do not assume the stronger `Store_ok`.
Object relations preserve types and allow exactly the mutations admitted by
SpecTec's extension relation. -/

namespace Exec.Spec

/-- Each old address remains present and its object is related. -/
def ObjectsExtend {α : Type} [Inhabited α] (R : α → α → Prop)
    (xs ys : List α) : Prop :=
  xs.length ≤ ys.length ∧ ∀ i, i < xs.length → R xs[i]! ys[i]!

private theorem append_old {α : Type} [Inhabited α] (xs ys : List α)
    (i : Nat) (hi : i < xs.length) : (xs ++ ys)[i]! = xs[i]! := by
  simp only [getElem!_pos xs i hi,
    getElem!_pos (xs ++ ys) i (by simp only [List.length_append]; omega),
    List.getElem_append_left hi]

/-- Appending objects preserves every existing address. -/
theorem objectsExtend_append {α : Type} [Inhabited α] {R : α → α → Prop}
    {xs : List α} (ys : List α) (h : ObjectsExtend R xs xs) :
    ObjectsExtend R xs (xs ++ ys) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  rw [append_old xs ys i hi]
  exact h.2 i hi

/-- A single object replacement leaves all other addresses unchanged. -/
theorem objectsExtend_set {α : Type} [Inhabited α] {R : α → α → Prop}
    {xs : List α} (i : Nat) (value : α) (h : ObjectsExtend R xs xs)
    (hv : i < xs.length → R xs[i]! value) :
    ObjectsExtend R xs (xs.set i value) := by
  refine ⟨by simp, ?_⟩
  intro j hj
  by_cases hij : i = j
  · subst j
    simpa [getElem!_pos, hj] using hv hj
  · simpa [getElem!_pos, hj, List.getElem_set, hij, Ne.symm hij] using h.2 j hj

/-- Pointwise object extension is the generated store relation. -/
theorem extend_store_of_objects {s t : store} (hs : wf_store s) (ht : wf_store t)
    (hglobal : ObjectsExtend Extend_globalinst s.GLOBALS t.GLOBALS)
    (hmem : ObjectsExtend Extend_meminst s.MEMS t.MEMS)
    (htable : ObjectsExtend Extend_tableinst s.TABLES t.TABLES)
    (hfunc : ObjectsExtend Extend_funcinst s.FUNCS t.FUNCS)
    (hdata : ObjectsExtend Extend_datainst s.DATAS t.DATAS)
    (helem : ObjectsExtend Extend_eleminst s.ELEMS t.ELEMS)
    : Extend_store s t := by
  apply Extend_store.mk_Extend_store
  · intro i hi; exact List.mem_range.mp hi
  · intro i hi; exact lt_of_lt_of_le (List.mem_range.mp hi) hglobal.1
  · intro i hi; exact hglobal.2 i (List.mem_range.mp hi)
  · intro i hi; exact List.mem_range.mp hi
  · intro i hi; exact lt_of_lt_of_le (List.mem_range.mp hi) hmem.1
  · intro i hi; exact hmem.2 i (List.mem_range.mp hi)
  · intro i hi; exact List.mem_range.mp hi
  · intro i hi; exact lt_of_lt_of_le (List.mem_range.mp hi) htable.1
  · intro i hi; exact htable.2 i (List.mem_range.mp hi)
  · intro i hi; exact List.mem_range.mp hi
  · intro i hi; exact lt_of_lt_of_le (List.mem_range.mp hi) hfunc.1
  · intro i hi; exact hfunc.2 i (List.mem_range.mp hi)
  · intro i hi; exact List.mem_range.mp hi
  · intro i hi; exact lt_of_lt_of_le (List.mem_range.mp hi) hdata.1
  · intro i hi; exact hdata.2 i (List.mem_range.mp hi)
  · intro i hi; exact List.mem_range.mp hi
  · intro i hi; exact lt_of_lt_of_le (List.mem_range.mp hi) helem.1
  · intro i hi; exact helem.2 i (List.mem_range.mp hi)
  · exact hs
  · exact ht

/-- Extract the pointwise description without using generated metatheorems. -/
theorem extend_store_objects {s t : store} (h : Extend_store s t) :
    ObjectsExtend Extend_globalinst s.GLOBALS t.GLOBALS ∧
    ObjectsExtend Extend_meminst s.MEMS t.MEMS ∧
    ObjectsExtend Extend_tableinst s.TABLES t.TABLES ∧
    ObjectsExtend Extend_funcinst s.FUNCS t.FUNCS ∧
    ObjectsExtend Extend_datainst s.DATAS t.DATAS ∧
    ObjectsExtend Extend_eleminst s.ELEMS t.ELEMS := by
  cases h with
  | mk_Extend_store ag bg rg am bm rm atb bt rt af bf rf ad bd rd ae be re hs ht =>
    have len {α β : Type} (xs : List α) (ys : List β)
        (h : Forall (fun i => i < ys.length) (List.range xs.length)) :
        xs.length ≤ ys.length := by
      by_contra hn
      have hi := h ys.length (List.mem_range.mpr (by omega))
      omega
    exact ⟨⟨len _ _ bg, fun i hi => rg i (List.mem_range.mpr hi)⟩,
      ⟨len _ _ bm, fun i hi => rm i (List.mem_range.mpr hi)⟩,
      ⟨len _ _ bt, fun i hi => rt i (List.mem_range.mpr hi)⟩,
      ⟨len _ _ bf, fun i hi => rf i (List.mem_range.mpr hi)⟩,
      ⟨len _ _ bd, fun i hi => rd i (List.mem_range.mpr hi)⟩,
      ⟨len _ _ be, fun i hi => re i (List.mem_range.mpr hi)⟩⟩

/-- Allocate any collection of objects by appending to the six address spaces. -/
theorem extend_store_append (s added : store) (hs : wf_store s)
    (ht : wf_store ⟨s.FUNCS ++ added.FUNCS, s.GLOBALS ++ added.GLOBALS,
      s.TABLES ++ added.TABLES, s.MEMS ++ added.MEMS,
      s.ELEMS ++ added.ELEMS, s.DATAS ++ added.DATAS⟩) :
    Extend_store s ⟨s.FUNCS ++ added.FUNCS, s.GLOBALS ++ added.GLOBALS,
      s.TABLES ++ added.TABLES, s.MEMS ++ added.MEMS,
      s.ELEMS ++ added.ELEMS, s.DATAS ++ added.DATAS⟩ := by
  obtain ⟨hg, hm, ht', hf, hd, he⟩ := extend_store_objects (extend_store_refl s hs)
  exact extend_store_of_objects hs ht
    (objectsExtend_append _ hg) (objectsExtend_append _ hm)
    (objectsExtend_append _ ht') (objectsExtend_append _ hf)
    (objectsExtend_append _ hd) (objectsExtend_append _ he)

/-- Replace one global object by an extension, preserving all other addresses. -/
theorem extend_store_set_global (s : store) (i : Nat) (value : globalinst)
    (hs : wf_store s) (ht : wf_store { s with GLOBALS := s.GLOBALS.set i value })
    (hv : i < s.GLOBALS.length → Extend_globalinst s.GLOBALS[i]! value) :
    Extend_store s { s with GLOBALS := s.GLOBALS.set i value } := by
  obtain ⟨hg, hm, ht', hf, hd, he⟩ := extend_store_objects (extend_store_refl s hs)
  exact extend_store_of_objects hs ht
    (objectsExtend_set i value hg hv) hm ht' hf hd he

/-- Replace one mem object by an extension, preserving all other addresses. -/
theorem extend_store_set_mem (s : store) (i : Nat) (value : meminst)
    (hs : wf_store s) (ht : wf_store { s with MEMS := s.MEMS.set i value })
    (hv : i < s.MEMS.length → Extend_meminst s.MEMS[i]! value) :
    Extend_store s { s with MEMS := s.MEMS.set i value } := by
  obtain ⟨hg, hm, ht', hf, hd, he⟩ := extend_store_objects (extend_store_refl s hs)
  exact extend_store_of_objects hs ht
    hg (objectsExtend_set i value hm hv) ht' hf hd he

/-- Replace one table object by an extension, preserving all other addresses. -/
theorem extend_store_set_table (s : store) (i : Nat) (value : tableinst)
    (hs : wf_store s) (ht : wf_store { s with TABLES := s.TABLES.set i value })
    (hv : i < s.TABLES.length → Extend_tableinst s.TABLES[i]! value) :
    Extend_store s { s with TABLES := s.TABLES.set i value } := by
  obtain ⟨hg, hm, ht', hf, hd, he⟩ := extend_store_objects (extend_store_refl s hs)
  exact extend_store_of_objects hs ht
    hg hm (objectsExtend_set i value ht' hv) hf hd he

/-- Replace one func object by an extension, preserving all other addresses. -/
theorem extend_store_set_func (s : store) (i : Nat) (value : funcinst)
    (hs : wf_store s) (ht : wf_store { s with FUNCS := s.FUNCS.set i value })
    (hv : i < s.FUNCS.length → Extend_funcinst s.FUNCS[i]! value) :
    Extend_store s { s with FUNCS := s.FUNCS.set i value } := by
  obtain ⟨hg, hm, ht', hf, hd, he⟩ := extend_store_objects (extend_store_refl s hs)
  exact extend_store_of_objects hs ht
    hg hm ht' (objectsExtend_set i value hf hv) hd he

/-- Replace one data object by an extension, preserving all other addresses. -/
theorem extend_store_set_data (s : store) (i : Nat) (value : datainst)
    (hs : wf_store s) (ht : wf_store { s with DATAS := s.DATAS.set i value })
    (hv : i < s.DATAS.length → Extend_datainst s.DATAS[i]! value) :
    Extend_store s { s with DATAS := s.DATAS.set i value } := by
  obtain ⟨hg, hm, ht', hf, hd, he⟩ := extend_store_objects (extend_store_refl s hs)
  exact extend_store_of_objects hs ht
    hg hm ht' hf (objectsExtend_set i value hd hv) he

/-- Replace one elem object by an extension, preserving all other addresses. -/
theorem extend_store_set_elem (s : store) (i : Nat) (value : eleminst)
    (hs : wf_store s) (ht : wf_store { s with ELEMS := s.ELEMS.set i value })
    (hv : i < s.ELEMS.length → Extend_eleminst s.ELEMS[i]! value) :
    Extend_store s { s with ELEMS := s.ELEMS.set i value } := by
  obtain ⟨hg, hm, ht', hf, hd, he⟩ := extend_store_objects (extend_store_refl s hs)
  exact extend_store_of_objects hs ht
    hg hm ht' hf hd (objectsExtend_set i value he hv)

theorem extend_global_mutable (ty : valtype) (before after : val)
    (hb : wf_globalinst ⟨⟨some .MUT, ty⟩, before⟩)
    (ha : wf_globalinst ⟨⟨some .MUT, ty⟩, after⟩) :
    Extend_globalinst ⟨⟨some .MUT, ty⟩, before⟩ ⟨⟨some .MUT, ty⟩, after⟩ := by
  exact .mk_Extend_globalinst _ _ _ _ (Or.inl rfl) hb ha

/-- Memory contents may change freely while the declared minimum and length grow. -/
theorem extend_mem_contents (n n' : Nat) (maximum : Option Nat) (before after : List byte)
    (hn : n ≤ n') (hl : before.length ≤ after.length)
    (hb : wf_meminst ⟨.PAGE ⟨.mk_uN n, OMap uN.mk_uN maximum⟩, before⟩)
    (ha : wf_meminst ⟨.PAGE ⟨.mk_uN n', OMap uN.mk_uN maximum⟩, after⟩) :
    Extend_meminst ⟨.PAGE ⟨.mk_uN n, OMap uN.mk_uN maximum⟩, before⟩
      ⟨.PAGE ⟨.mk_uN n', OMap uN.mk_uN maximum⟩, after⟩ := by
  exact .mk_Extend_meminst _ _ _ _ _ hn hl hb ha

/-- Table mutation preserves its reference type and maximum, and never shrinks. -/
theorem extend_table_contents (n n' : Nat) (maximum : Option Nat) (ty : reftype)
    (before after : List ref) (hn : n ≤ n') (hl : before.length ≤ after.length)
    (hb : wf_tableinst ⟨⟨⟨.mk_uN n, OMap uN.mk_uN maximum⟩, ty⟩, before⟩)
    (ha : wf_tableinst ⟨⟨⟨.mk_uN n', OMap uN.mk_uN maximum⟩, ty⟩, after⟩) :
    Extend_tableinst ⟨⟨⟨.mk_uN n, OMap uN.mk_uN maximum⟩, ty⟩, before⟩
      ⟨⟨⟨.mk_uN n', OMap uN.mk_uN maximum⟩, ty⟩, after⟩ := by
  exact .mk_Extend_tableinst _ _ _ _ _ _ hn hl hb ha

end Exec.Spec
