import Itasca.Binary.Wasm2.References
import Itasca.Wasm2.References.ReadersTotal

open Aeneas Aeneas.Std

namespace Itasca

/-- Accepted literal type tags identify their exact single-byte encoding. -/
theorem code.take_reference_type.spec (st : code.OpIterState) (data : Slice U8) :
    code.take_reference_type st data ⦃ r => r.2.vals = st.vals ∧ r.2.ctrls = st.ctrls ∧
      ∀ ty : types.ElemType, r.1 = .Ok ty →
        Wasm1.BytesAt data st.pos [Wasm2.ReferencesBinary.referenceByte ty] r.2.pos ⦄ := by
  by_cases hp : st.pos.val < data.length
  · obtain ⟨_, hr, next, rfl, hn⟩ := WP.spec_imp_exists (reader.read_byte.spec data st.pos hp)
    simp only [code.take_reference_type, hr, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    conv => arg 1; whnf
    split
    all_goals simp only [WP.spec_ok]
    all_goals refine ⟨trivial, trivial, ?_⟩
    all_goals intro ty he
    all_goals try cases he
    all_goals exact Wasm1.BytesAt.byte data st.pos next _ hp (by assumption) hn
  · simp [code.take_reference_type, reader.read_byte.eof data st.pos (by omega),
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- Accepted literal type tags identify their exact single-byte encoding. -/
theorem code.take_value_type.spec (st : code.OpIterState) (data : Slice U8) :
    code.take_value_type st data ⦃ r => r.2.vals = st.vals ∧ r.2.ctrls = st.ctrls ∧
      ∀ ty : types.ValueType, r.1 = .Ok ty →
        Wasm1.BytesAt data st.pos [Wasm2.valueByte ty] r.2.pos ⦄ := by
  by_cases hp : st.pos.val < data.length
  · obtain ⟨_, hr, next, rfl, hn⟩ := WP.spec_imp_exists (reader.read_byte.spec data st.pos hp)
    simp only [code.take_value_type, hr, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    conv => arg 1; whnf
    split
    all_goals simp only [WP.spec_ok]
    all_goals refine ⟨trivial, trivial, ?_⟩
    all_goals intro ty he
    all_goals try cases he
    all_goals exact Wasm1.BytesAt.byte data st.pos next _ hp (by assumption) hn
  · simp [code.take_value_type, reader.read_byte.eof data st.pos (by omega),
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem types.ElemType.value_type.eq (rt : types.ElemType) :
    types.ElemType.value_type rt = .ok (ModuleConstants.referenceValueType rt) := by
  cases rt <;> rfl

/-- A decoded index resolves to its actual reference element type. -/
theorem code.take_table.spec (st : code.OpIterState) (data : Slice U8) (env : module.Env) :
    code.take_table st data env ⦃ r => r.2.vals = st.vals ∧ r.2.ctrls = st.ctrls ∧
      ∀ index ty, r.1 = .Ok (index, ty) → Leb128.Decoded data st.pos index r.2.pos ∧
        ∃ hi : index.val < env.table_types.val.length,
          ty = ModuleConstants.referenceValueType env.table_types.val[index.val].elem ⦄ := by
  obtain ⟨⟨r, s⟩, hr, hv, hc, hd⟩ := WP.spec_imp_exists (code.take_index.spec st data)
  dsimp only at hv hc hd
  cases r with
  | Err e =>
    simp [code.take_table, hr, hv, hc, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok index =>
    by_cases hi : index.val < env.table_types.val.length
    · have hix : (UScalar.cast .Usize index).val < env.table_types.val.length := by simpa using hi
      obtain ⟨entry, hget, heq⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.index_usize_spec env.table_types (UScalar.cast .Usize index) hix)
      have he : env.table_types.val[index.val] = entry := by simpa using heq.symm
      have hn := Nat.not_le_of_gt hi
      rw [WP.spec_equiv_exists]
      refine ⟨(.Ok (index, ModuleConstants.referenceValueType entry.elem), s), ?_, hv, hc, ?_⟩
      · simp [code.take_table, hr, lift, hn, hget, types.ElemType.value_type.eq,
          core.result.Result.Insts.CoreOpsTry.branch]
      · intro other ty hok
        cases hok
        exact ⟨hd, hi, by rw [he]⟩
    · have hn := Nat.le_of_not_gt hi
      simp [code.take_table, hr, hv, hc, lift, hn, core.result.Result.Insts.CoreOpsTry.branch]

/-- A decoded index resolves to its actual reference element type. -/
theorem code.take_element.spec (st : code.OpIterState) (data : Slice U8) (env : module.Env) :
    code.take_element st data env ⦃ r => r.2.vals = st.vals ∧ r.2.ctrls = st.ctrls ∧
      ∀ index ty, r.1 = .Ok (index, ty) → Leb128.Decoded data st.pos index r.2.pos ∧
        ∃ hi : index.val < env.elements.val.length,
          ty = ModuleConstants.referenceValueType env.elements.val[index.val].elem ⦄ := by
  obtain ⟨⟨r, s⟩, hr, hv, hc, hd⟩ := WP.spec_imp_exists (code.take_index.spec st data)
  dsimp only at hv hc hd
  cases r with
  | Err e =>
    simp [code.take_element, hr, hv, hc, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok index =>
    by_cases hi : index.val < env.elements.val.length
    · have hix : (UScalar.cast .Usize index).val < env.elements.val.length := by simpa using hi
      obtain ⟨entry, hget, heq⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.index_usize_spec env.elements (UScalar.cast .Usize index) hix)
      have he : env.elements.val[index.val] = entry := by simpa using heq.symm
      have hn := Nat.not_le_of_gt hi
      rw [WP.spec_equiv_exists]
      refine ⟨(.Ok (index, ModuleConstants.referenceValueType entry.elem), s), ?_, hv, hc, ?_⟩
      · simp [code.take_element, hr, lift, hn, hget, types.ElemType.value_type.eq,
          core.result.Result.Insts.CoreOpsTry.branch]
      · intro other ty hok
        cases hok
        exact ⟨hd, hi, by rw [he]⟩
    · have hn := Nat.le_of_not_gt hi
      simp [code.take_element, hr, hv, hc, lift, hn, core.result.Result.Insts.CoreOpsTry.branch]

/-- Data instructions require the explicit data-count section and its bound. -/
theorem code.take_data_index.spec (st : code.OpIterState) (data : Slice U8) (env : module.Env) :
    code.take_data_index st data env ⦃ r => r.2.vals = st.vals ∧ r.2.ctrls = st.ctrls ∧
      ∀ index, r.1 = .Ok index → Leb128.Decoded data st.pos index r.2.pos ∧
        ∃ count, env.data_count = some count ∧ index.val < count.val ⦄ := by
  obtain ⟨⟨r, s⟩, hr, hv, hc, hd⟩ := WP.spec_imp_exists (code.take_index.spec st data)
  dsimp only at hv hc hd
  cases r with
  | Err e =>
    simp [code.take_data_index, hr, hv, hc, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok index =>
    cases hcount : env.data_count with
    | none => simp [code.take_data_index, hr, hv, hc, hcount, core.result.Result.Insts.CoreOpsTry.branch]
    | some count =>
      by_cases hi : index.val < count.val
      · have hn := Nat.not_le_of_gt hi
        rw [WP.spec_equiv_exists]
        refine ⟨(.Ok index, s), ?_, hv, hc, ?_⟩
        · simp [code.take_data_index, hr, hcount, hn, core.result.Result.Insts.CoreOpsTry.branch]
        · intro other he
          cases he
          exact ⟨hd, count, rfl, hi⟩
      · have hn := Nat.le_of_not_gt hi
        simp [code.take_data_index, hr, hv, hc, hcount, hn, core.result.Result.Insts.CoreOpsTry.branch]

/-- Bulk memory instructions consume one literal reserved byte and require memory zero. -/
theorem code.read_bulk_memory.spec (st : code.OpIterState) (data : Slice U8) (env : module.Env) :
    code.read_bulk_memory st data env ⦃ r => r.2.vals = st.vals ∧ r.2.ctrls = st.ctrls ∧
      (r.1 = .Ok () → Wasm1.BytesAt data st.pos [0#u8] r.2.pos ∧ 0 < env.mem_types.val.length) ⦄ := by
  obtain ⟨⟨r, s⟩, hr, hv, hc, hd⟩ := WP.spec_imp_exists (code.read_reserved_zero.spec st data)
  dsimp only at hv hc hd
  cases r with
  | Err e =>
    simp [code.read_bulk_memory, hr, hv, hc, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok u =>
    cases u
    by_cases hm : env.mem_types.val = []
    · simp [code.read_bulk_memory, hr, hv, hc, alloc.vec.Vec.is_empty, hm,
        core.result.Result.Insts.CoreOpsTry.branch]
    · have hn : env.mem_types.val.isEmpty = false := by simp [hm]
      rw [WP.spec_equiv_exists]
      refine ⟨(.Ok (), s), ?_, hv, hc, ?_⟩
      · simp [code.read_bulk_memory, hr, alloc.vec.Vec.is_empty, hn,
          core.result.Result.Insts.CoreOpsTry.branch]
      · intro _
        obtain ⟨hp, hz, hpos⟩ := hd
        exact ⟨Wasm1.BytesAt.byte data st.pos s.pos 0#u8 hp hz hpos, List.length_pos_iff.mpr hm⟩

/-- Successful `ref.func` decoding establishes the independent declaration
condition in addition to ordinary function-index bounds. -/
theorem code.read_ref_func.spec (st : code.OpIterState) (data : Slice U8)
    (env : module.Env) (hsize : st.vals.val.length < Usize.max) :
    code.read_ref_func st data env ⦃ r =>
      r.2.ctrls = st.ctrls ∧ ∀ index, r.1 = .Ok index →
        Leb128.Decoded data st.pos index r.2.pos ∧ index.val < env.func_types.val.length ∧
        DeclaredReferences.Instruction
          (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) (.REF_FUNC (.mk_uN index.val)) ∧
        r.2.vals.val = st.vals.val ++ [.Val .FuncRef] ⦄ := by
  obtain ⟨⟨r, s⟩, hr, hv, hc, hd⟩ := WP.spec_imp_exists (code.take_index.spec st data)
  dsimp only at hv hc hd
  cases r with
  | Err e =>
    simp [code.read_ref_func, hr, hc, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok index =>
    by_cases hi : index.val < env.func_types.val.length
    · have hn := Nat.not_le_of_gt hi
      by_cases hm : index ∈ env.declared_funcs.val
      · obtain ⟨out, hp, hvals, hctrls, hpos⟩ := WP.spec_imp_exists
          (code.push_val.spec s (.Val .FuncRef) (by simpa [hv] using hsize))
        rw [WP.spec_equiv_exists]
        refine ⟨(.Ok index, out), ?_, hctrls.trans hc, ?_⟩
        · simp [code.read_ref_func, hr, core.result.Result.Insts.CoreOpsTry.branch,
            lift, hn, module.Env.declares_function.eq, hm, hp]
        intro other he
        cases he
        exact ⟨by simpa [hpos] using hd, hi,
          DeclaredReferences.Instruction.ref_func_iff.mpr (List.mem_map.mpr ⟨index, hm, rfl⟩),
          by simpa [hv] using hvals⟩
      · simp [code.read_ref_func, hr, hc, lift, hn, module.Env.declares_function.eq, hm,
          core.result.Result.Insts.CoreOpsTry.branch]
    · have hn := Nat.le_of_not_gt hi
      simp [code.read_ref_func, hr, hc, lift, hn, core.result.Result.Insts.CoreOpsTry.branch]

end Itasca
