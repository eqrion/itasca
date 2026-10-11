import Itasca.MultiValue.BulkOperands

open Aeneas Aeneas.Std

namespace Itasca.MultiValue

theorem memoryInitMetadata.spec (st : code.OpIterState) (data : Slice U8) (env : module.Env) :
    memoryInitMetadata st data env ⦃ r => r.2.vals = st.vals ∧ r.2.ctrls = st.ctrls ∧
      ∀ idx, r.1 = .Ok idx → ∃ bytes,
        Wasm.BytesAt data st.pos (bytes ++ [0#u8]) r.2.pos ∧ Leb128.Encoding bytes idx.val ∧
        (∃ count, env.data_count = some count ∧ idx.val < count.val) ∧ 0 < env.mem_types.val.length ⦄ := by
  obtain ⟨⟨res, middle⟩, hr, hv, hc, hd⟩ := WP.spec_imp_exists (code.take_data_index.spec st data env)
  dsimp only at hv hc hd
  cases res with
  | Err e => simp [memoryInitMetadata, hr, hv, hc]
  | Ok idx =>
    obtain ⟨⟨res, out⟩, ho, hov, hoc, hod⟩ := WP.spec_imp_exists (code.read_bulk_memory.spec middle data env)
    dsimp only at hov hoc hod
    cases res with
    | Err e => simp [memoryInitMetadata, hr, ho, hov, hoc, hv, hc]
    | Ok u =>
      cases u
      rw [WP.spec_equiv_exists]
      refine ⟨(.Ok idx, out), by simp [memoryInitMetadata, hr, ho], hov.trans hv, hoc.trans hc, ?_⟩
      intro other he
      cases he
      obtain ⟨⟨bytes, hbs, hbl, hbb, hbe⟩, hcount⟩ := hd idx rfl
      obtain ⟨hzero, hmem⟩ := hod rfl
      exact ⟨bytes, (Wasm.BytesAt.mk hbs hbl hbb).append hzero, hbe, hcount, hmem⟩

theorem memoryCopyMetadata.spec (st : code.OpIterState) (data : Slice U8) (env : module.Env) :
    memoryCopyMetadata st data env ⦃ r => r.2.vals = st.vals ∧ r.2.ctrls = st.ctrls ∧
      (r.1 = .Ok () → Wasm.BytesAt data st.pos [0#u8, 0#u8] r.2.pos ∧ 0 < env.mem_types.val.length) ⦄ := by
  obtain ⟨⟨res, middle⟩, hr, hv, hc, hd⟩ := WP.spec_imp_exists (code.read_bulk_memory.spec st data env)
  dsimp only at hv hc hd
  cases res with
  | Err e => simp [memoryCopyMetadata, hr, hv, hc]
  | Ok u =>
    cases u
    simp only [memoryCopyMetadata, hr, bind_ok]
    apply WP.spec_mono (code.read_reserved_zero.spec middle data)
    rintro ⟨res, out⟩ ⟨hov, hoc, hod⟩
    refine ⟨hov.trans hv, hoc.trans hc, ?_⟩
    intro hok
    dsimp only at hov hoc hod hok
    subst res
    obtain ⟨hp, hz, hpos⟩ := hod
    exact ⟨(hd rfl).1.append (Wasm.BytesAt.byte data middle.pos out.pos _ hp hz hpos), (hd rfl).2⟩

/-- Sequential reference-index decoding preserves each byte span and compares
the two resolved element types before the fixed operand checker runs. -/
theorem referencePairMetadata.spec
    (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (first : Result (core.result.Result (U32 × types.ValueType) error.OpError × code.OpIterState))
    (P : U32 → types.ValueType → Usize → Prop)
    (hf : first ⦃ r => r.2.vals = st.vals ∧ r.2.ctrls = st.ctrls ∧
      ∀ idx ty, r.1 = .Ok (idx, ty) → P idx ty r.2.pos ⦄) :
    referencePairMetadata first data env ⦃ r => r.2.vals = st.vals ∧ r.2.ctrls = st.ctrls ∧
      ∀ i j, r.1 = .Ok (i, j) → ∃ middle ty,
        P i ty middle ∧ Leb128.Decoded data middle j r.2.pos ∧
        ∃ hi : j.val < env.table_types.val.length,
          ty = ModuleConstants.referenceValueType env.table_types.val[j.val].elem ⦄ := by
  classical
  obtain ⟨⟨res, middle⟩, hr, hv, hc, hd⟩ := WP.spec_imp_exists hf
  dsimp only at hv hc hd
  cases res with
  | Err e => simp [referencePairMetadata, hr, hv, hc]
  | Ok pair =>
    obtain ⟨i, ty⟩ := pair
    obtain ⟨⟨res, out⟩, ho, hov, hoc, hod⟩ := WP.spec_imp_exists (code.take_table.spec middle data env)
    dsimp only at hov hoc hod
    cases res with
    | Err e => simp [referencePairMetadata, hr, ho, hov, hoc, hv, hc]
    | Ok pair =>
      obtain ⟨j, ty'⟩ := pair
      by_cases he : ty = ty'
      · subst ty'
        rw [WP.spec_equiv_exists]
        refine ⟨(.Ok (i, j), out), by simp [referencePairMetadata, hr, ho],
          hov.trans hv, hoc.trans hc, ?_⟩
        intro otherI otherJ hok
        cases hok
        exact ⟨middle.pos, ty, hd i ty rfl, hod j ty rfl⟩
      · simp [referencePairMetadata, hr, ho, he, hov, hoc, hv, hc]

end Itasca.MultiValue
