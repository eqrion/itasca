import Itasca.Runtime.Spec.Mutation
namespace Itasca.Runtime.Spec

theorem extend_store_wf {s t : store} (h : Extend_store s t) : wf_store s ∧ wf_store t := by
  cases h; exact ⟨by assumption, by assumption⟩

theorem extend_func_eq {a b : funcinst} (h : Extend_funcinst a b) : b = a := by
  cases h; rfl

theorem extend_global_type {a b : globalinst} (h : Extend_globalinst a b) : b.TYPE = a.TYPE := by
  cases h; rfl

private theorem limits_grow_sub (n n' : Nat) (mx : Option Nat) (growth : n ≤ n')
    (old : wf_limits ⟨.mk_uN n, OMap uN.mk_uN mx⟩)
    (fresh : wf_limits ⟨.mk_uN n', OMap uN.mk_uN mx⟩) :
    Limits_sub ⟨.mk_uN n', OMap uN.mk_uN mx⟩ ⟨.mk_uN n, OMap uN.mk_uN mx⟩ := by
  cases mx with
  | none => exact .eps n' n growth fresh old
  | some maximum =>
    exact .max n' maximum n (some maximum) growth (by simp [Forall]) fresh old

theorem extend_mem_type_sub {a b : meminst} (h : Extend_meminst a b) :
    Memtype_sub b.TYPE a.TYPE := by
  cases h with
  | mk_Extend_meminst n mx bytes n' bytes' growth _ old fresh =>
    have wo : wf_memtype (.PAGE ⟨.mk_uN n, OMap uN.mk_uN mx⟩) := by cases old; assumption
    have wn : wf_memtype (.PAGE ⟨.mk_uN n', OMap uN.mk_uN mx⟩) := by cases fresh; assumption
    exact .mk_Memtype_sub _ _ (limits_grow_sub n n' mx growth
      (by cases wo; assumption) (by cases wn; assumption)) wn wo

theorem extend_table_type_sub {a b : tableinst} (h : Extend_tableinst a b) :
    Tabletype_sub b.TYPE a.TYPE := by
  cases h with
  | mk_Extend_tableinst n mx rt refs n' refs' growth _ old fresh =>
    have wo : wf_tabletype ⟨⟨.mk_uN n, OMap uN.mk_uN mx⟩, rt⟩ := by cases old; assumption
    have wn : wf_tabletype ⟨⟨.mk_uN n', OMap uN.mk_uN mx⟩, rt⟩ := by cases fresh; assumption
    exact .mk_Tabletype_sub _ rt _ (limits_grow_sub n n' mx growth
      (by cases wo; assumption) (by cases wn; assumption)) wn wo

private theorem memtype_sub_wf {a b : memtype} (h : Memtype_sub a b) : wf_memtype a := by
  cases h; assumption

private theorem tabletype_sub_wf {a b : tabletype} (h : Tabletype_sub a b) : wf_tabletype a := by
  cases h; assumption

/-- Extension preserves every typed external address, including declared
memory/table bounds when the underlying object grows. -/
theorem externaddr_ok_extend {s t : store} (extension : Extend_store s t)
    {address : externaddr} {ty : externtype} (typed : Externaddr_ok s address ty) :
    Externaddr_ok t address ty := by
  obtain ⟨globals, memories, tables, functions, _, _⟩ := extend_store_objects extension
  have fresh := (extend_store_wf extension).2
  induction typed with
  | global address value bound found _ wt =>
    have equal := extend_global_type (globals.2 address bound)
    rw [found] at equal
    rw [← equal] at wt ⊢
    exact .global t address _ (bound.trans_le globals.1) rfl fresh wt
  | func address value bound found _ wt =>
    have equal := extend_func_eq (functions.2 address bound)
    rw [found] at equal
    rw [← equal] at wt ⊢
    exact .func t address _ (bound.trans_le functions.1) rfl fresh wt
  | mem address value bound found _ wt =>
    have sub := extend_mem_type_sub (memories.2 address bound)
    rw [found] at sub
    have newType : wf_externtype (.MEM t.MEMS[address]!.TYPE) := by
      constructor; exact memtype_sub_wf sub
    exact .sub t (.MEM address) (.MEM value.TYPE) (.MEM t.MEMS[address]!.TYPE)
      (.mem t address _ (bound.trans_le memories.1) rfl fresh newType)
      (.mem _ _ sub newType wt) fresh wt newType
  | table address value bound found _ wt =>
    have sub := extend_table_type_sub (tables.2 address bound)
    rw [found] at sub
    have newType : wf_externtype (.TABLE t.TABLES[address]!.TYPE) := by
      constructor; exact tabletype_sub_wf sub
    exact .sub t (.TABLE address) (.TABLE value.TYPE) (.TABLE t.TABLES[address]!.TYPE)
      (.table t address _ (bound.trans_le tables.1) rfl fresh newType)
      (.table _ _ sub newType wt) fresh wt newType
  | sub address ty actual prior sub _ wt wa ih =>
    exact .sub t address ty actual ih sub fresh wt wa

theorem ref_ok_extend {s t : store} (extension : Extend_store s t)
    {value : ref} {ty : reftype} (typed : Ref_ok s value ty) : Ref_ok t value ty := by
  have fresh := (extend_store_wf extension).2
  cases typed with
  | null ty _ => exact .null t ty fresh
  | func address ty addressTyped _ wf =>
    exact .func t address ty (externaddr_ok_extend extension addressTyped) fresh wf
  | extern address _ => exact .extern t address fresh

/-- Dropping a segment preserves its semantic instance typing. -/
theorem eleminst_ok_extend {s t : store} (extension : Extend_store s t)
    {a b : eleminst} {ty : elemtype} (objects : Extend_eleminst a b)
    (typed : Eleminst_ok s a ty) : Eleminst_ok t b ty := by
  cases objects with
  | mk_Extend_eleminst rt refs refs' contents =>
    cases typed with
    | mk_Eleminst_ok _ _ values bound _ =>
      rcases contents with rfl | rfl
      · exact .mk_Eleminst_ok t _ refs (fun value member => ref_ok_extend extension (values value member))
          bound (extend_store_wf extension).2
      · exact .mk_Eleminst_ok t _ [] (by simp [Forall]) (by norm_num) (extend_store_wf extension).2

theorem datainst_ok_extend {s t : store} (extension : Extend_store s t)
    {a b : datainst} {ty : datatype} (objects : Extend_datainst a b)
    (typed : Datainst_ok s a ty) : Datainst_ok t b ty := by
  cases objects with
  | mk_Extend_datainst bytes bytes' contents old fresh =>
    cases typed with
    | mk_Datainst_ok _ bound _ _ =>
      rcases contents with rfl | rfl
      · exact .mk_Datainst_ok t bytes bound (extend_store_wf extension).2 fresh
      · exact .mk_Datainst_ok t [] (by norm_num) (extend_store_wf extension).2 fresh
end Itasca.Runtime.Spec
namespace Itasca.Runtime.Spec

theorem function_lookup_extend {s t : store} (extension : Extend_store s t)
    {index : Nat} {fn : funcinst} (found : s.FUNCS[index]? = some fn) :
    t.FUNCS[index]? = some fn := by
  have functions := (extend_store_objects extension).2.2.2.1
  obtain ⟨bound, equal⟩ := List.getElem?_eq_some_iff.mp found
  have retained := extend_func_eq (functions.2 index bound)
  have room := bound.trans_le functions.1
  rw [getElem!_pos s.FUNCS index bound, getElem!_pos t.FUNCS index room] at retained
  exact List.getElem?_eq_some_iff.mpr ⟨room, retained.trans equal⟩

theorem element_lookup_extend {s t : store} (extension : Extend_store s t)
    {index : Nat} {entry : eleminst} {ty : elemtype}
    (found : s.ELEMS[index]? = some entry) (typed : Eleminst_ok s entry ty) :
    ∃ fresh, t.ELEMS[index]? = some fresh ∧ Eleminst_ok t fresh ty := by
  have elements := (extend_store_objects extension).2.2.2.2.2
  obtain ⟨bound, equal⟩ := List.getElem?_eq_some_iff.mp found
  have retained := elements.2 index bound
  have room := bound.trans_le elements.1
  rw [getElem!_pos s.ELEMS index bound, equal] at retained
  refine ⟨t.ELEMS[index]!, ?_, eleminst_ok_extend extension retained typed⟩
  simp [getElem!_pos t.ELEMS index room]

theorem data_lookup_extend {s t : store} (extension : Extend_store s t)
    {index : Nat} {entry : datainst} {ty : datatype}
    (found : s.DATAS[index]? = some entry) (typed : Datainst_ok s entry ty) :
    ∃ fresh, t.DATAS[index]? = some fresh ∧ Datainst_ok t fresh ty := by
  have segments := (extend_store_objects extension).2.2.2.2.1
  obtain ⟨bound, equal⟩ := List.getElem?_eq_some_iff.mp found
  have retained := segments.2 index bound
  have room := bound.trans_le segments.1
  rw [getElem!_pos s.DATAS index bound, equal] at retained
  refine ⟨t.DATAS[index]!, ?_, datainst_ok_extend extension retained typed⟩
  simp [getElem!_pos t.DATAS index room]
end Itasca.Runtime.Spec
