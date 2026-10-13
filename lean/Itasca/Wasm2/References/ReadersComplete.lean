import Itasca.Wasm2.Bulk.Operands
import Itasca.Binary.Wasm1.EncodingComplete
import Itasca.Support.EnvTranslation

open Aeneas Aeneas.Std

namespace Itasca

theorem code.take_reference_type.complete (st : code.OpIterState) (data : Slice U8)
    (rt : types.ElemType) (next : Usize)
    (hb : Wasm1.BytesAt data st.pos [Wasm2.ReferencesBinary.referenceByte rt] next) :
    code.take_reference_type st data = .ok (.Ok rt, {st with pos := next}) := by
  have hr := hb.read_byte
  cases rt <;> simp [code.take_reference_type, hr, Wasm2.ReferencesBinary.referenceByte,
    core.result.Result.Insts.CoreOpsTry.branch]

theorem code.take_value_type.complete (st : code.OpIterState) (data : Slice U8)
    (ty : types.ValueType) (next : Usize)
    (hb : Wasm1.BytesAt data st.pos [Wasm2.valueByte ty] next) :
    code.take_value_type st data = .ok (.Ok ty, {st with pos := next}) := by
  have hr := hb.read_byte
  cases ty <;> simp [code.take_value_type, hr, Wasm2.valueByte,
    core.result.Result.Insts.CoreOpsTry.branch]

theorem code.take_table.complete (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (idx : U32) (next : Usize) (hd : Leb128.Decoded data st.pos idx next)
    (hi : idx.val < env.table_types.val.length) :
    code.take_table st data env = .ok (.Ok (idx,
      ModuleConstants.referenceValueType env.table_types.val[idx.val].elem), {st with pos := next}) := by
  obtain ⟨bs, hbs, hbl, hbb, hbe⟩ := hd
  have hr := (Wasm1.BytesAt.mk hbs hbl hbb).take_index st idx hbe
  have hix : (UScalar.cast .Usize idx).val < env.table_types.val.length := by simpa using hi
  obtain ⟨tt, hget, heq⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec env.table_types (UScalar.cast .Usize idx) hix)
  have he : env.table_types.val[idx.val] = tt := by simpa using heq.symm
  have hn := Nat.not_le_of_gt hi
  simp [code.take_table, hr, lift, hn, hget, he, types.ElemType.value_type.eq,
    core.result.Result.Insts.CoreOpsTry.branch]

theorem code.take_element.complete (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (idx : U32) (next : Usize) (hd : Leb128.Decoded data st.pos idx next)
    (hi : idx.val < env.elements.val.length) :
    code.take_element st data env = .ok (.Ok (idx,
      ModuleConstants.referenceValueType env.elements.val[idx.val].elem), {st with pos := next}) := by
  obtain ⟨bs, hbs, hbl, hbb, hbe⟩ := hd
  have hr := (Wasm1.BytesAt.mk hbs hbl hbb).take_index st idx hbe
  have hix : (UScalar.cast .Usize idx).val < env.elements.val.length := by simpa using hi
  obtain ⟨tt, hget, heq⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec env.elements (UScalar.cast .Usize idx) hix)
  have he : env.elements.val[idx.val] = tt := by simpa using heq.symm
  have hn := Nat.not_le_of_gt hi
  simp [code.take_element, hr, lift, hn, hget, he, types.ElemType.value_type.eq,
    core.result.Result.Insts.CoreOpsTry.branch]

theorem code.take_data_index.complete (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (idx count : U32) (next : Usize) (hd : Leb128.Decoded data st.pos idx next)
    (hc : env.data_count = some count) (hi : idx.val < count.val) :
    code.take_data_index st data env = .ok (.Ok idx, {st with pos := next}) := by
  obtain ⟨bs, hbs, hbl, hbb, hbe⟩ := hd
  have hr := (Wasm1.BytesAt.mk hbs hbl hbb).take_index st idx hbe
  have hn := Nat.not_le_of_gt hi
  simp [code.take_data_index, hr, hc, hn, core.result.Result.Insts.CoreOpsTry.branch]

theorem code.read_reserved_zero.complete (st : code.OpIterState) (data : Slice U8)
    (next : Usize) (hb : Wasm1.BytesAt data st.pos [0#u8] next) :
    code.read_reserved_zero st data = .ok (.Ok (), {st with pos := next}) := by
  simp [code.read_reserved_zero, hb.read_byte, core.result.Result.Insts.CoreOpsTry.branch]

theorem code.read_bulk_memory.complete (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (next : Usize) (hb : Wasm1.BytesAt data st.pos [0#u8] next)
    (hm : 0 < env.mem_types.val.length) :
    code.read_bulk_memory st data env = .ok (.Ok (), {st with pos := next}) := by
  have hn : env.mem_types.val.isEmpty = false := by simp [List.length_pos_iff.mp hm]
  simp [code.read_bulk_memory, code.read_reserved_zero.complete st data next hb,
    alloc.vec.Vec.is_empty, hn, core.result.Result.Insts.CoreOpsTry.branch]

end Itasca

namespace Itasca.EnvTranslation

/-- Generated table lookup supplies the concrete reader's bound and value type. -/
theorem Matches.table_reference {env ctx C} (h : Matches env ctx C)
    (idx : U32) (lim : limits) (rt : reftype) (hi : idx.val < C.TABLES.length)
    (ht : C.TABLES[idx.val]! = .mk_tabletype lim rt) :
    ∃ hv : idx.val < env.table_types.val.length,
      Translate.valueType (ModuleConstants.referenceValueType env.table_types.val[idx.val].elem) =
        valtype_reftype rt := by
  obtain ⟨tt, hv, htt, htype⟩ := h.table_lookup idx _ hi ht
  refine ⟨hv, ?_⟩
  rw [htt]
  cases he : tt.elem <;> cases rt <;> simp_all [tableType, Translate.referenceType,
    ModuleConstants.referenceValueType, Translate.valueType, valtype_reftype]

end Itasca.EnvTranslation

namespace Itasca.EnvTranslation

theorem Matches.element_reference {env ctx C} (h : Matches env ctx C)
    (idx : U32) (rt : reftype) (hi : idx.val < C.ELEMS.length)
    (ht : C.ELEMS[idx.val]! = rt) :
    ∃ hv : idx.val < env.elements.val.length,
      Translate.valueType (ModuleConstants.referenceValueType env.elements.val[idx.val].elem) =
        valtype_reftype rt := by
  have hv : idx.val < env.elements.val.length := by simpa [h.elems, elementTypes] using hi
  have he : Translate.referenceType env.elements.val[idx.val].elem = rt := by
    rw [h.elems] at ht
    change (env.elements.val.map (fun e => Translate.referenceType e.elem))[idx.val]! = rt at ht
    rw [getElem!_pos _ _ (by simpa using hv), List.getElem_map] at ht
    exact ht
  refine ⟨hv, ?_⟩
  rw [← he]
  cases env.elements.val[idx.val].elem <;> rfl

theorem Matches.data_bound {env ctx C} (h : Matches env ctx C)
    (idx : U32) (hi : idx.val < C.DATAS.length) :
    ∃ count, env.data_count = some count ∧ idx.val < count.val := by
  rw [h.datas] at hi
  cases hc : env.data_count with
  | none => simp [dataTypes, hc] at hi
  | some count => exact ⟨count, rfl, by simpa [dataTypes, hc] using hi⟩

end Itasca.EnvTranslation
