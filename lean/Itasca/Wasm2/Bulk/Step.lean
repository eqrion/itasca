import Itasca.Wasm2.Bulk.Readers
import Itasca.Wasm2.References.Step

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

theorem Pending.memory_fill {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 11#u32 next)
    (hsize : st.core.vals.val.length < Usize.max) :
    code.read_memory_fill {st.core with pos := next} data env ⦃ r =>
      (∃ a, r.1 = .Ok a) → p.After {st with core := r.2} ⦄ := by
  rw [code.read_memory_fill.fixed]
  apply p.metadata_read (code.read_bulk_memory {st.core with pos := next} data env)
    (fun _ => [.I32, .I32, .I32]) (fun _ => none) id (fun _ => .MEMORY_FILL) ?_ ?_ ?_ hsize
  · apply WP.spec_mono (code.read_bulk_memory.spec {st.core with pos := next} data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    refine ⟨hv, hc, ?_⟩
    intro u hok
    cases u
    obtain ⟨hb, _⟩ := hd hok
    obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
    exact At.of_immediate p.inbounds hbyte p.pos (.bulk 11#u32 hpe .memoryFill)
      ((Wasm1.BytesAt.mk hp hpl hpb).append hb)
  · exact fun _ => .instr_case_64
  · rintro u ⟨decoded, hrun⟩ C hC
    cases u
    have hspec := code.read_bulk_memory.spec {st.core with pos := next} data env
    rw [hrun, WP.spec_ok] at hspec
    simpa [Simd.inputTypes, Simd.outputTypes, Translate.valueType] using hC.memory_fill (hspec.2.2 rfl).2

theorem Pending.memory_copy {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 10#u32 next)
    (hsize : st.core.vals.val.length < Usize.max) :
    code.read_memory_copy {st.core with pos := next} data env ⦃ r =>
      (∃ a, r.1 = .Ok a) → p.After {st with core := r.2} ⦄ := by
  rw [code.read_memory_copy.fixed]
  apply p.metadata_read (memoryCopyMetadata {st.core with pos := next} data env)
    (fun _ => [.I32, .I32, .I32]) (fun _ => none) id (fun _ => .MEMORY_COPY) ?_ ?_ ?_ hsize
  · apply WP.spec_mono (memoryCopyMetadata.spec {st.core with pos := next} data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    refine ⟨hv, hc, ?_⟩
    intro u hok
    cases u
    obtain ⟨hb, _⟩ := hd hok
    obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
    exact At.of_immediate p.inbounds hbyte p.pos (.bulk 10#u32 hpe .memoryCopy)
      ((Wasm1.BytesAt.mk hp hpl hpb).append hb)
  · exact fun _ => .instr_case_65
  · rintro u ⟨decoded, hrun⟩ C hC
    cases u
    have hspec := memoryCopyMetadata.spec {st.core with pos := next} data env
    rw [hrun, WP.spec_ok] at hspec
    simpa [Simd.inputTypes, Simd.outputTypes, Translate.valueType] using hC.memory_copy (hspec.2.2 rfl).2

theorem Pending.memory_init {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 8#u32 next)
    (hsize : st.core.vals.val.length < Usize.max) :
    code.read_memory_init {st.core with pos := next} data env ⦃ r =>
      (∃ a, r.1 = .Ok a) → p.After {st with core := r.2} ⦄ := by
  rw [code.read_memory_init.fixed]
  apply p.metadata_read (memoryInitMetadata {st.core with pos := next} data env)
    (fun _ => [.I32, .I32, .I32]) (fun _ => none) id
    (fun idx => .MEMORY_INIT (.mk_uN idx.val)) ?_ ?_ ?_ hsize
  · apply WP.spec_mono (memoryInitMetadata.spec {st.core with pos := next} data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    refine ⟨hv, hc, ?_⟩
    intro idx hok
    obtain ⟨bytes, hb, he, _⟩ := hd idx hok
    obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
    exact At.of_immediate p.inbounds hbyte p.pos (.bulk 8#u32 hpe (.memoryInit idx he))
      ((Wasm1.BytesAt.mk hp hpl hpb).append hb)
  · exact fun idx => .instr_case_66 _ (EnvTranslation.index_wf idx)
  · rintro idx ⟨decoded, hrun⟩ C hC
    have hspec := memoryInitMetadata.spec {st.core with pos := next} data env
    rw [hrun, WP.spec_ok] at hspec
    obtain ⟨_, _, _, ⟨count, hcount, hi⟩, hm⟩ := hspec.2.2 idx rfl
    simpa [Simd.inputTypes, Simd.outputTypes, Translate.valueType] using hC.memory_init idx count hcount hi hm

theorem reference_value_injective {a b : types.ElemType}
    (h : ModuleConstants.referenceValueType a = ModuleConstants.referenceValueType b) : a = b := by
  cases a <;> cases b <;> simp_all [ModuleConstants.referenceValueType]

theorem Pending.table_init {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 12#u32 next)
    (hsize : st.core.vals.val.length < Usize.max) :
    code.read_table_init {st.core with pos := next} data env ⦃ r =>
      (∃ a, r.1 = .Ok a) → p.After {st with core := r.2} ⦄ := by
  rw [code.read_table_init.fixed]
  have hmetadata := referencePairMetadata.spec {st.core with pos := next} data env
    (code.take_element {st.core with pos := next} data env)
    (fun i ty pos => Leb128.Decoded data next i pos ∧
      ∃ hi : i.val < env.elements.val.length,
        ty = ModuleConstants.referenceValueType env.elements.val[i.val].elem)
    (code.take_element.spec {st.core with pos := next} data env)
  apply p.metadata_read _ (fun _ => [.I32, .I32, .I32]) (fun _ => none) id
    (fun a => .TABLE_INIT (.mk_uN a.2.val) (.mk_uN a.1.val)) ?_ ?_ ?_ hsize
  · apply WP.spec_mono hmetadata
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    refine ⟨hv, hc, ?_⟩
    rintro ⟨i, j⟩ hok
    obtain ⟨middle, ty, ⟨hdi, _⟩, hdj, _⟩ := hd i j hok
    obtain ⟨ibs, his, hil, hib, hie⟩ := hdi
    obtain ⟨jbs, hjs, hjl, hjb, hje⟩ := hdj
    obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
    exact At.of_immediate p.inbounds hbyte p.pos (.bulk 12#u32 hpe (.tableInit i j hie hje))
      ((Wasm1.BytesAt.mk hp hpl hpb).append ((Wasm1.BytesAt.mk his hil hib).append ⟨hjs, hjl, hjb⟩))
  · exact fun a => .instr_case_54 _ _ (EnvTranslation.index_wf a.2) (EnvTranslation.index_wf a.1)
  · rintro ⟨i, j⟩ ⟨decoded, hrun⟩ C hC
    rw [hrun, WP.spec_ok] at hmetadata
    obtain ⟨middle, ty, ⟨_, hi, hity⟩, _, hj, hjty⟩ := hmetadata.2.2 i j rfl
    simpa [Simd.inputTypes, Simd.outputTypes, Translate.valueType] using
      hC.table_init j i env.table_types.val[j.val] env.elements.val[i.val] hj hi rfl rfl (reference_value_injective (hity.symm.trans hjty))

theorem Pending.table_copy {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 14#u32 next)
    (hsize : st.core.vals.val.length < Usize.max) :
    code.read_table_copy {st.core with pos := next} data env ⦃ r =>
      (∃ a, r.1 = .Ok a) → p.After {st with core := r.2} ⦄ := by
  rw [code.read_table_copy.fixed]
  have hmetadata := referencePairMetadata.spec {st.core with pos := next} data env
    (code.take_table {st.core with pos := next} data env)
    (fun i ty pos => Leb128.Decoded data next i pos ∧
      ∃ hi : i.val < env.table_types.val.length,
        ty = ModuleConstants.referenceValueType env.table_types.val[i.val].elem)
    (code.take_table.spec {st.core with pos := next} data env)
  apply p.metadata_read _ (fun _ => [.I32, .I32, .I32]) (fun _ => none) id
    (fun a => .TABLE_COPY (.mk_uN a.1.val) (.mk_uN a.2.val)) ?_ ?_ ?_ hsize
  · apply WP.spec_mono hmetadata
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    refine ⟨hv, hc, ?_⟩
    rintro ⟨i, j⟩ hok
    obtain ⟨middle, ty, ⟨hdi, _⟩, hdj, _⟩ := hd i j hok
    obtain ⟨ibs, his, hil, hib, hie⟩ := hdi
    obtain ⟨jbs, hjs, hjl, hjb, hje⟩ := hdj
    obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
    exact At.of_immediate p.inbounds hbyte p.pos (.bulk 14#u32 hpe (.tableCopy i j hie hje))
      ((Wasm1.BytesAt.mk hp hpl hpb).append ((Wasm1.BytesAt.mk his hil hib).append ⟨hjs, hjl, hjb⟩))
  · exact fun a => .instr_case_53 _ _ (EnvTranslation.index_wf a.1) (EnvTranslation.index_wf a.2)
  · rintro ⟨i, j⟩ ⟨decoded, hrun⟩ C hC
    rw [hrun, WP.spec_ok] at hmetadata
    obtain ⟨middle, ty, ⟨_, hi, hity⟩, _, hj, hjty⟩ := hmetadata.2.2 i j rfl
    simpa [Simd.inputTypes, Simd.outputTypes, Translate.valueType] using
      hC.table_copy i j env.table_types.val[i.val] env.table_types.val[j.val] hi hj rfl rfl (reference_value_injective (hjty.symm.trans hity))

end Itasca.Wasm2
