import Itasca.Binary.Wasm2.References
import Itasca.Binary.Wasm2.Bulk

/-!
# Environment matching for reference and bulk instructions

Lemmas about `EnvTranslation.Matches`, the agreement between a runtime `module.Env` and a
SpecTec context. Each `Matches.table_get`, `Matches.table_copy`, `Matches.memory_init`, ... turns
bounds on the runtime environment into the corresponding `Instr_ok` judgment for the reference,
table and bulk-memory instructions.
-/

open Aeneas Aeneas.Std

namespace Itasca.EnvTranslation

/-- A runtime table entry supplies the corresponding generated lookup. -/
theorem Matches.table_entry {env ctx C} (h : Matches env ctx C)
    (idx : U32) (tt : types.TableType) (hi : idx.val < env.table_types.val.length)
    (ht : env.table_types.val[idx.val] = tt) :
    idx.val < C.TABLES.length ∧ C.TABLES[idx.val]! = tableType tt := by
  rw [h.tables]
  constructor
  · simpa using hi
  · rw [getElem!_pos _ _ (by simpa using hi), List.getElem_map, ht]

theorem Matches.element_entry {env ctx C} (h : Matches env ctx C)
    (idx : U32) (elem : module.Element) (hi : idx.val < env.elements.val.length)
    (ht : env.elements.val[idx.val] = elem) :
    idx.val < C.ELEMS.length ∧ C.ELEMS[idx.val]! = Translate.referenceType elem.elem := by
  rw [h.elems]
  simp only [elementTypes]
  constructor
  · simpa using hi
  · rw [getElem!_pos _ _ (by simpa using hi), List.getElem_map, ht]

theorem Matches.data_entry {env ctx C} (h : Matches env ctx C)
    (idx count : U32) (hc : env.data_count = some count) (hi : idx.val < count.val) :
    idx.val < C.DATAS.length ∧ C.DATAS[idx.val]! = .OK := by
  rw [h.datas]
  simp only [dataTypes, hc, Option.map_some, Option.getD_some, List.length_replicate]
  exact ⟨hi, trivial⟩

theorem Matches.ref_func {env ctx C} (h : Matches env ctx C)
    (idx : U32) (hi : idx.val < env.func_types.val.length) :
    Instr_ok C (.REF_FUNC (.mk_uN idx.val)) (.mk_functype (.mk_list []) (.mk_list [.FUNCREF])) := by
  apply Instr_ok.ref_func _ _ (funcType env.func_types.val[idx.val])
  · simpa [h.funcs, proj_uN_0] using hi
  · simp only [h.funcs, proj_uN_0]
    rw [getElem!_pos _ _ (by simpa using hi), List.getElem_map]
  · exact h.wf
  · exact .instr_case_41 _ (index_wf idx)

theorem Matches.table_get {env ctx C} (h : Matches env ctx C)
    (idx : U32) (tt : types.TableType) (hi : idx.val < env.table_types.val.length)
    (ht : env.table_types.val[idx.val] = tt) :
    Instr_ok C (.TABLE_GET (.mk_uN idx.val))
      (.mk_functype (.mk_list [.I32]) (.mk_list [valtype_reftype (Translate.referenceType tt.elem)])) := by
  obtain ⟨hb, he⟩ := h.table_entry idx tt hi ht
  exact .table_get _ _ _ _ hb he h.wf (.instr_case_48 _ (index_wf idx)) (tableType_wf tt)

theorem Matches.table_set {env ctx C} (h : Matches env ctx C)
    (idx : U32) (tt : types.TableType) (hi : idx.val < env.table_types.val.length)
    (ht : env.table_types.val[idx.val] = tt) :
    Instr_ok C (.TABLE_SET (.mk_uN idx.val))
      (.mk_functype (.mk_list [.I32, valtype_reftype (Translate.referenceType tt.elem)]) (.mk_list [])) := by
  obtain ⟨hb, he⟩ := h.table_entry idx tt hi ht
  exact .table_set _ _ _ _ hb he h.wf (.instr_case_49 _ (index_wf idx)) (tableType_wf tt)

theorem Matches.table_size {env ctx C} (h : Matches env ctx C)
    (idx : U32) (tt : types.TableType) (hi : idx.val < env.table_types.val.length)
    (ht : env.table_types.val[idx.val] = tt) :
    Instr_ok C (.TABLE_SIZE (.mk_uN idx.val))
      (.mk_functype (.mk_list []) (.mk_list [.I32])) := by
  obtain ⟨hb, he⟩ := h.table_entry idx tt hi ht
  exact .table_size _ _ _ _ hb he h.wf (.instr_case_50 _ (index_wf idx)) (tableType_wf tt)

theorem Matches.table_grow {env ctx C} (h : Matches env ctx C)
    (idx : U32) (tt : types.TableType) (hi : idx.val < env.table_types.val.length)
    (ht : env.table_types.val[idx.val] = tt) :
    Instr_ok C (.TABLE_GROW (.mk_uN idx.val))
      (.mk_functype (.mk_list [valtype_reftype (Translate.referenceType tt.elem), .I32]) (.mk_list [.I32])) := by
  obtain ⟨hb, he⟩ := h.table_entry idx tt hi ht
  exact .table_grow _ _ _ _ hb he h.wf (.instr_case_51 _ (index_wf idx)) (tableType_wf tt)

theorem Matches.table_fill {env ctx C} (h : Matches env ctx C)
    (idx : U32) (tt : types.TableType) (hi : idx.val < env.table_types.val.length)
    (ht : env.table_types.val[idx.val] = tt) :
    Instr_ok C (.TABLE_FILL (.mk_uN idx.val))
      (.mk_functype (.mk_list [.I32, valtype_reftype (Translate.referenceType tt.elem), .I32]) (.mk_list [])) := by
  obtain ⟨hb, he⟩ := h.table_entry idx tt hi ht
  exact .table_fill _ _ _ _ hb he h.wf (.instr_case_52 _ (index_wf idx)) (tableType_wf tt)

theorem Matches.table_copy {env ctx C} (h : Matches env ctx C)
    (destination source : U32) (dst src : types.TableType)
    (hd : destination.val < env.table_types.val.length) (hs : source.val < env.table_types.val.length)
    (htd : env.table_types.val[destination.val] = dst) (hts : env.table_types.val[source.val] = src)
    (htype : src.elem = dst.elem) :
    Instr_ok C (.TABLE_COPY (.mk_uN destination.val) (.mk_uN source.val))
      (.mk_functype (.mk_list [.I32, .I32, .I32]) (.mk_list [])) := by
  obtain ⟨hdb, hde⟩ := h.table_entry destination dst hd htd
  obtain ⟨hsb, hse⟩ := h.table_entry source src hs hts
  exact .table_copy C _ _ (limitsType dst.limits) (Translate.referenceType dst.elem)
    (limitsType src.limits) hdb hde hsb (by simpa [tableType, htype, proj_uN_0] using hse) h.wf
    (.instr_case_53 _ _ (index_wf destination) (index_wf source)) (tableType_wf dst)
    (by simpa [tableType, htype] using tableType_wf src)

theorem Matches.table_init {env ctx C} (h : Matches env ctx C)
    (table element : U32) (tt : types.TableType) (elem : module.Element)
    (ht : table.val < env.table_types.val.length) (he : element.val < env.elements.val.length)
    (htt : env.table_types.val[table.val] = tt) (hee : env.elements.val[element.val] = elem)
    (htype : elem.elem = tt.elem) :
    Instr_ok C (.TABLE_INIT (.mk_uN table.val) (.mk_uN element.val))
      (.mk_functype (.mk_list [.I32, .I32, .I32]) (.mk_list [])) := by
  obtain ⟨htb, hte⟩ := h.table_entry table tt ht htt
  obtain ⟨heb, hee⟩ := h.element_entry element elem he hee
  exact .table_init _ _ _ _ _ htb hte heb (by simpa [htype, proj_uN_0] using hee) h.wf
    (.instr_case_54 _ _ (index_wf table) (index_wf element)) (tableType_wf tt)

theorem Matches.elem_drop {env ctx C} (h : Matches env ctx C)
    (idx : U32) (elem : module.Element) (hi : idx.val < env.elements.val.length)
    (ht : env.elements.val[idx.val] = elem) :
    Instr_ok C (.ELEM_DROP (.mk_uN idx.val)) (.mk_functype (.mk_list []) (.mk_list [])) := by
  obtain ⟨hb, he⟩ := h.element_entry idx elem hi ht
  exact .elem_drop _ _ _ hb he h.wf (.instr_case_55 _ (index_wf idx))

theorem Matches.memory_copy {env ctx C} (h : Matches env ctx C)
    (hmem : 0 < env.mem_types.val.length) :
    Instr_ok C .MEMORY_COPY (.mk_functype (.mk_list [.I32, .I32, .I32]) (.mk_list [])) := by
  apply Instr_ok.memory_copy _ (memType env.mem_types.val[0])
  · simpa [h.mems] using hmem
  · simp only [h.mems]
    rw [getElem!_pos _ _ (by simpa using hmem), List.getElem_map]
  · exact h.wf
  · exact memType_wf _
  · exact .instr_case_65

theorem Matches.memory_fill {env ctx C} (h : Matches env ctx C)
    (hmem : 0 < env.mem_types.val.length) :
    Instr_ok C .MEMORY_FILL (.mk_functype (.mk_list [.I32, .I32, .I32]) (.mk_list [])) := by
  apply Instr_ok.memory_fill _ (memType env.mem_types.val[0])
  · simpa [h.mems] using hmem
  · simp only [h.mems]
    rw [getElem!_pos _ _ (by simpa using hmem), List.getElem_map]
  · exact h.wf
  · exact memType_wf _
  · exact .instr_case_64

theorem Matches.memory_init {env ctx C} (h : Matches env ctx C)
    (idx count : U32) (hc : env.data_count = some count) (hi : idx.val < count.val)
    (hmem : 0 < env.mem_types.val.length) :
    Instr_ok C (.MEMORY_INIT (.mk_uN idx.val))
      (.mk_functype (.mk_list [.I32, .I32, .I32]) (.mk_list [])) := by
  obtain ⟨hb, he⟩ := h.data_entry idx count hc hi
  apply Instr_ok.memory_init _ _ (memType env.mem_types.val[0])
  · simpa [h.mems] using hmem
  · simp only [h.mems]
    rw [getElem!_pos _ _ (by simpa using hmem), List.getElem_map]
  · exact hb
  · exact he
  · exact h.wf
  · exact memType_wf _
  · exact .instr_case_66 _ (index_wf idx)

theorem Matches.data_drop {env ctx C} (h : Matches env ctx C)
    (idx count : U32) (hc : env.data_count = some count) (hi : idx.val < count.val) :
    Instr_ok C (.DATA_DROP (.mk_uN idx.val)) (.mk_functype (.mk_list []) (.mk_list [])) := by
  obtain ⟨hb, he⟩ := h.data_entry idx count hc hi
  exact .data_drop _ _ hb he h.wf (.instr_case_67 _ (index_wf idx))

end Itasca.EnvTranslation
