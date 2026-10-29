import Itasca.Runtime.Compiler.Body.Reader.Replay.Metadata
import Itasca.Wasm2.Bulk.Step
import Itasca.Runtime.Compiler.Body.Reader.Stateful.StatefulPost

/-!
Stateful reader postconditions for reference, memory/table and segment operations. Per-opcode reader effects establish the shared stateful metadata certificates.
-/

/-! ## Reader Stateful Bulk -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2

theorem reader_memory_fill_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 11#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : Unit) (out : code.OpIterState)
    (accepted : code.read_memory_fill {st.core with pos := next} data env = .ok (.Ok value,out)) :
    MetadataReaderPost p (code.read_bulk_memory {st.core with pos := next} data env) (fun _ => [.I32,.I32,.I32]) (fun _ => none) id
      (fun _ => .MEMORY_FILL) value out := by
  rw [code.read_memory_fill.fixed] at accepted
  apply reader_metadata_wasm2 p (code.read_bulk_memory {st.core with pos := next} data env) (fun _ => [.I32,.I32,.I32]) (fun _ => none) id
    (fun _ => .MEMORY_FILL) ?_ ?_ ?_ ?_ hsize value out accepted
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
  · intro a _
    simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]

theorem reader_memory_copy_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 10#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : Unit) (out : code.OpIterState)
    (accepted : code.read_memory_copy {st.core with pos := next} data env = .ok (.Ok value,out)) :
    MetadataReaderPost p (memoryCopyMetadata {st.core with pos := next} data env) (fun _ => [.I32,.I32,.I32]) (fun _ => none) id
      (fun _ => .MEMORY_COPY) value out := by
  rw [code.read_memory_copy.fixed] at accepted
  apply reader_metadata_wasm2 p (memoryCopyMetadata {st.core with pos := next} data env) (fun _ => [.I32,.I32,.I32]) (fun _ => none) id
    (fun _ => .MEMORY_COPY) ?_ ?_ ?_ ?_ hsize value out accepted
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
  · intro a _
    simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]

theorem reader_memory_init_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 8#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.read_memory_init {st.core with pos := next} data env = .ok (.Ok value,out)) :
    MetadataReaderPost p (memoryInitMetadata {st.core with pos := next} data env) (fun _ => [.I32,.I32,.I32]) (fun _ => none) id
      (fun idx => .MEMORY_INIT (.mk_uN idx.val)) value out := by
  rw [code.read_memory_init.fixed] at accepted
  apply reader_metadata_wasm2 p (memoryInitMetadata {st.core with pos := next} data env) (fun _ => [.I32,.I32,.I32]) (fun _ => none) id
    (fun idx => .MEMORY_INIT (.mk_uN idx.val)) ?_ ?_ ?_ ?_ hsize value out accepted
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
  · intro a _
    simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]

theorem reader_table_init_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 12#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32 × U32) (out : code.OpIterState)
    (accepted : code.read_table_init {st.core with pos := next} data env = .ok (.Ok value,out)) :
    MetadataReaderPost p (referencePairMetadata (code.take_element {st.core with pos := next} data env) data env) (fun _ => [.I32,.I32,.I32]) (fun _ => none) id
      (fun a => .TABLE_INIT (.mk_uN a.2.val) (.mk_uN a.1.val)) value out := by
  rw [code.read_table_init.fixed] at accepted
  have hmetadata := referencePairMetadata.spec {st.core with pos := next} data env
    (code.take_element {st.core with pos := next} data env)
    (fun i ty pos => Leb128.Decoded data next i pos ∧
      ∃ hi : i.val < env.elements.val.length,
        ty = ModuleConstants.referenceValueType env.elements.val[i.val].elem)
    (code.take_element.spec {st.core with pos := next} data env)
  apply reader_metadata_wasm2 p (referencePairMetadata (code.take_element {st.core with pos := next} data env) data env) (fun _ => [.I32,.I32,.I32]) (fun _ => none) id
    (fun a => .TABLE_INIT (.mk_uN a.2.val) (.mk_uN a.1.val)) ?_ ?_ ?_ ?_ hsize value out accepted
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
  · intro a _
    simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]

theorem reader_table_copy_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 14#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32 × U32) (out : code.OpIterState)
    (accepted : code.read_table_copy {st.core with pos := next} data env = .ok (.Ok value,out)) :
    MetadataReaderPost p (referencePairMetadata (code.take_table {st.core with pos := next} data env) data env) (fun _ => [.I32,.I32,.I32]) (fun _ => none) id
      (fun a => .TABLE_COPY (.mk_uN a.1.val) (.mk_uN a.2.val)) value out := by
  rw [code.read_table_copy.fixed] at accepted
  have hmetadata := referencePairMetadata.spec {st.core with pos := next} data env
    (code.take_table {st.core with pos := next} data env)
    (fun i ty pos => Leb128.Decoded data next i pos ∧
      ∃ hi : i.val < env.table_types.val.length,
        ty = ModuleConstants.referenceValueType env.table_types.val[i.val].elem)
    (code.take_table.spec {st.core with pos := next} data env)
  apply reader_metadata_wasm2 p (referencePairMetadata (code.take_table {st.core with pos := next} data env) data env) (fun _ => [.I32,.I32,.I32]) (fun _ => none) id
    (fun a => .TABLE_COPY (.mk_uN a.1.val) (.mk_uN a.2.val)) ?_ ?_ ?_ ?_ hsize value out accepted
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
  · intro a _
    simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]

end Itasca.Runtime.Compiler

end

/-! ## Reader Stateful Metadata -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2

theorem reader_table_get_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 37#u8)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.read_table_get st.core data env = .ok (.Ok value,out)) :
    MetadataReaderPost p (code.take_table st.core data env) (fun _ => [.I32]) (fun a => some a.2) Prod.fst
      (fun a => .TABLE_GET (.mk_uN a.1.val)) value out := by
  rw [code.read_table_get.fixed] at accepted
  apply reader_metadata_wasm2 p (code.take_table st.core data env) (fun _ => [.I32]) (fun a => some a.2) Prod.fst
    (fun a => .TABLE_GET (.mk_uN a.1.val)) ?_ ?_ ?_ ?_ hsize value out accepted
  · apply WP.spec_mono (code.take_table.spec st.core data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    dsimp only at hv hc hd ⊢
    refine ⟨hv, hc, ?_⟩
    rintro ⟨idx, ty⟩ hok
    obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := (hd idx ty hok).1
    exact At.of_immediate p.inbounds hbyte p.pos (.reference (.tableGet idx hencoding))
      ⟨hbytes, hlen, hbound⟩
  · exact fun a => .instr_case_48 _ (EnvTranslation.index_wf a.1)
  · rintro ⟨idx, ty⟩ ⟨decoded, hrun⟩ C hC
    have hspec := code.take_table.spec st.core data env
    rw [hrun, WP.spec_ok] at hspec
    obtain ⟨_, hi, hty⟩ := hspec.2.2 idx ty rfl
    have htyped := hC.table_get idx env.table_types.val[idx.val] hi rfl
    simpa [Simd.inputTypes, Simd.outputTypes, hty, reference_value_translation, show Translate.valueType .I32 = valtype.I32 from rfl]
      using htyped
  · intro a _
    simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]

theorem reader_table_set_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 38#u8)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.read_table_set st.core data env = .ok (.Ok value,out)) :
    MetadataReaderPost p (code.take_table st.core data env) (fun a => [a.2, .I32]) (fun _ => none) Prod.fst
      (fun a => .TABLE_SET (.mk_uN a.1.val)) value out := by
  rw [code.read_table_set.fixed] at accepted
  apply reader_metadata_wasm2 p (code.take_table st.core data env) (fun a => [a.2, .I32]) (fun _ => none) Prod.fst
    (fun a => .TABLE_SET (.mk_uN a.1.val)) ?_ ?_ ?_ ?_ hsize value out accepted
  · apply WP.spec_mono (code.take_table.spec st.core data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    dsimp only at hv hc hd ⊢
    refine ⟨hv, hc, ?_⟩
    rintro ⟨idx, ty⟩ hok
    obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := (hd idx ty hok).1
    exact At.of_immediate p.inbounds hbyte p.pos (.reference (.tableSet idx hencoding))
      ⟨hbytes, hlen, hbound⟩
  · exact fun a => .instr_case_49 _ (EnvTranslation.index_wf a.1)
  · rintro ⟨idx, ty⟩ ⟨decoded, hrun⟩ C hC
    have hspec := code.take_table.spec st.core data env
    rw [hrun, WP.spec_ok] at hspec
    obtain ⟨_, hi, hty⟩ := hspec.2.2 idx ty rfl
    have htyped := hC.table_set idx env.table_types.val[idx.val] hi rfl
    simpa [Simd.inputTypes, Simd.outputTypes, hty, reference_value_translation, show Translate.valueType .I32 = valtype.I32 from rfl]
      using htyped
  · intro a _
    simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]

theorem reader_ref_null_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 208#u8)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : types.ElemType) (out : code.OpIterState)
    (accepted : code.read_ref_null st.core data = .ok (.Ok value,out)) :
    MetadataReaderPost p (code.take_reference_type st.core data) (fun _ => []) (fun rt => some (ModuleConstants.referenceValueType rt)) id
      (fun rt => .REF_NULL (Translate.referenceType rt)) value out := by
  rw [code.read_ref_null.fixed] at accepted
  apply reader_metadata_wasm2 p (code.take_reference_type st.core data) (fun _ => []) (fun rt => some (ModuleConstants.referenceValueType rt)) id
    (fun rt => .REF_NULL (Translate.referenceType rt)) ?_ ?_ ?_ ?_ hsize value out accepted
  · apply WP.spec_mono (code.take_reference_type.spec st.core data)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    exact ⟨hv, hc, fun rt hok => At.of_immediate p.inbounds hbyte p.pos
      (.reference (.refNull rt)) (hd rt hok)⟩
  · exact fun _ => .instr_case_40 _
  · intro rt _ C hC
    simpa [Simd.inputTypes, Simd.outputTypes, reference_value_translation] using
      Instr_ok.ref_null C (Translate.referenceType rt) hC.wf (.instr_case_40 _)

  · intro a _
    simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]

theorem reader_table_grow_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 15#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.read_table_grow {st.core with pos := next} data env = .ok (.Ok value,out)) :
    MetadataReaderPost p (code.take_table {st.core with pos := next} data env) (fun a => [.I32, a.2]) (fun _ => some .I32) Prod.fst
      (fun a => .TABLE_GROW (.mk_uN a.1.val)) value out := by
  rw [code.read_table_grow.fixed] at accepted
  apply reader_metadata_wasm2 p (code.take_table {st.core with pos := next} data env) (fun a => [.I32, a.2]) (fun _ => some .I32) Prod.fst
    (fun a => .TABLE_GROW (.mk_uN a.1.val)) ?_ ?_ ?_ ?_ hsize value out accepted
  · apply WP.spec_mono (code.take_table.spec {st.core with pos := next} data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    dsimp only at hv hc hd ⊢
    refine ⟨hv, hc, ?_⟩
    rintro ⟨idx, ty⟩ hok
    obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := (hd idx ty hok).1
    obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
    exact At.of_immediate p.inbounds hbyte p.pos (.bulk 15#u32 hpe (.tableGrow idx hencoding))
      ((Wasm1.BytesAt.mk hp hpl hpb).append ⟨hbytes, hlen, hbound⟩)
  · exact fun a => .instr_case_51 _ (EnvTranslation.index_wf a.1)
  · rintro ⟨idx, ty⟩ ⟨decoded, hrun⟩ C hC
    have hspec := code.take_table.spec {st.core with pos := next} data env
    rw [hrun, WP.spec_ok] at hspec
    obtain ⟨_, hi, hty⟩ := hspec.2.2 idx ty rfl
    have htyped := hC.table_grow idx env.table_types.val[idx.val] hi rfl
    simpa [Simd.inputTypes, Simd.outputTypes, hty, reference_value_translation,
      show Translate.valueType .I32 = valtype.I32 from rfl] using htyped
  · intro a _
    simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]

theorem reader_table_size_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 16#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.read_table_size {st.core with pos := next} data env = .ok (.Ok value,out)) :
    MetadataReaderPost p (code.take_table {st.core with pos := next} data env) (fun _ => []) (fun _ => some .I32) Prod.fst
      (fun a => .TABLE_SIZE (.mk_uN a.1.val)) value out := by
  rw [code.read_table_size.fixed] at accepted
  apply reader_metadata_wasm2 p (code.take_table {st.core with pos := next} data env) (fun _ => []) (fun _ => some .I32) Prod.fst
    (fun a => .TABLE_SIZE (.mk_uN a.1.val)) ?_ ?_ ?_ ?_ hsize value out accepted
  · apply WP.spec_mono (code.take_table.spec {st.core with pos := next} data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    dsimp only at hv hc hd ⊢
    refine ⟨hv, hc, ?_⟩
    rintro ⟨idx, ty⟩ hok
    obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := (hd idx ty hok).1
    obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
    exact At.of_immediate p.inbounds hbyte p.pos (.bulk 16#u32 hpe (.tableSize idx hencoding))
      ((Wasm1.BytesAt.mk hp hpl hpb).append ⟨hbytes, hlen, hbound⟩)
  · exact fun a => .instr_case_50 _ (EnvTranslation.index_wf a.1)
  · rintro ⟨idx, ty⟩ ⟨decoded, hrun⟩ C hC
    have hspec := code.take_table.spec {st.core with pos := next} data env
    rw [hrun, WP.spec_ok] at hspec
    obtain ⟨_, hi, hty⟩ := hspec.2.2 idx ty rfl
    have htyped := hC.table_size idx env.table_types.val[idx.val] hi rfl
    simpa [Simd.inputTypes, Simd.outputTypes, hty, reference_value_translation,
      show Translate.valueType .I32 = valtype.I32 from rfl] using htyped
  · intro a _
    simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]

theorem reader_table_fill_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 17#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.read_table_fill {st.core with pos := next} data env = .ok (.Ok value,out)) :
    MetadataReaderPost p (code.take_table {st.core with pos := next} data env) (fun a => [.I32, a.2, .I32]) (fun _ => none) Prod.fst
      (fun a => .TABLE_FILL (.mk_uN a.1.val)) value out := by
  rw [code.read_table_fill.fixed] at accepted
  apply reader_metadata_wasm2 p (code.take_table {st.core with pos := next} data env) (fun a => [.I32, a.2, .I32]) (fun _ => none) Prod.fst
    (fun a => .TABLE_FILL (.mk_uN a.1.val)) ?_ ?_ ?_ ?_ hsize value out accepted
  · apply WP.spec_mono (code.take_table.spec {st.core with pos := next} data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    dsimp only at hv hc hd ⊢
    refine ⟨hv, hc, ?_⟩
    rintro ⟨idx, ty⟩ hok
    obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := (hd idx ty hok).1
    obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
    exact At.of_immediate p.inbounds hbyte p.pos (.bulk 17#u32 hpe (.tableFill idx hencoding))
      ((Wasm1.BytesAt.mk hp hpl hpb).append ⟨hbytes, hlen, hbound⟩)
  · exact fun a => .instr_case_52 _ (EnvTranslation.index_wf a.1)
  · rintro ⟨idx, ty⟩ ⟨decoded, hrun⟩ C hC
    have hspec := code.take_table.spec {st.core with pos := next} data env
    rw [hrun, WP.spec_ok] at hspec
    obtain ⟨_, hi, hty⟩ := hspec.2.2 idx ty rfl
    have htyped := hC.table_fill idx env.table_types.val[idx.val] hi rfl
    simpa [Simd.inputTypes, Simd.outputTypes, hty, reference_value_translation,
      show Translate.valueType .I32 = valtype.I32 from rfl] using htyped
  · intro a _
    simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]

theorem reader_data_drop_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 9#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.take_data_index {st.core with pos := next} data env = .ok (.Ok value,out)) :
    MetadataReaderPost p (code.take_data_index {st.core with pos := next} data env) (fun _ => []) (fun _ => none) id
      (fun idx => .DATA_DROP (.mk_uN idx.val)) value out := by
  rw [← metadataOperands.empty (code.take_data_index {st.core with pos := next} data env)] at accepted
  apply reader_metadata_wasm2 p (code.take_data_index {st.core with pos := next} data env) (fun _ => []) (fun _ => none) id
    (fun idx => .DATA_DROP (.mk_uN idx.val)) ?_ ?_ ?_ ?_ hsize value out accepted
  · apply WP.spec_mono (code.take_data_index.spec {st.core with pos := next} data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    refine ⟨hv, hc, ?_⟩
    intro idx hok
    obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := (hd idx hok).1
    obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
    exact At.of_immediate p.inbounds hbyte p.pos (.bulk 9#u32 hpe (.dataDrop idx hencoding))
      ((Wasm1.BytesAt.mk hp hpl hpb).append ⟨hbytes, hlen, hbound⟩)
  · exact fun a => .instr_case_67 _ (EnvTranslation.index_wf a)
  · rintro idx ⟨decoded, hrun⟩ C hC
    have hspec := code.take_data_index.spec {st.core with pos := next} data env
    rw [hrun, WP.spec_ok] at hspec
    obtain ⟨_, count, hc, hi⟩ := hspec.2.2 idx rfl
    exact hC.data_drop idx count hc hi
  · intro a _
    simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]

theorem reader_elem_drop_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 13#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32 × types.ValueType) (out : code.OpIterState)
    (accepted : code.take_element {st.core with pos := next} data env = .ok (.Ok value,out)) :
    MetadataReaderPost p (code.take_element {st.core with pos := next} data env) (fun _ => []) (fun _ => none) id
      (fun a => .ELEM_DROP (.mk_uN a.1.val)) value out := by
  rw [← metadataOperands.empty (code.take_element {st.core with pos := next} data env)] at accepted
  apply reader_metadata_wasm2 p (code.take_element {st.core with pos := next} data env) (fun _ => []) (fun _ => none) id
    (fun a => .ELEM_DROP (.mk_uN a.1.val)) ?_ ?_ ?_ ?_ hsize value out accepted
  · apply WP.spec_mono (code.take_element.spec {st.core with pos := next} data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    refine ⟨hv, hc, ?_⟩
    rintro ⟨idx, ty⟩ hok
    obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := (hd idx ty hok).1
    obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
    exact At.of_immediate p.inbounds hbyte p.pos (.bulk 13#u32 hpe (.elemDrop idx hencoding))
      ((Wasm1.BytesAt.mk hp hpl hpb).append ⟨hbytes, hlen, hbound⟩)
  · exact fun a => .instr_case_55 _ (EnvTranslation.index_wf a.1)
  · rintro ⟨idx, ty⟩ ⟨decoded, hrun⟩ C hC
    have hspec := code.take_element.spec {st.core with pos := next} data env
    rw [hrun, WP.spec_ok] at hspec
    obtain ⟨_, hi, hty⟩ := hspec.2.2 idx ty rfl
    exact hC.elem_drop idx env.elements.val[idx.val] hi rfl
  · intro a _
    simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]

end Itasca.Runtime.Compiler

end

/-! ## Reader Memory Metadata -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2

theorem memory_size_fixed (st : code.OpIterState) (data : Slice U8) (env : module.Env) :
    code.read_memory_size st data env = metadataOperands (code.read_bulk_memory st data env)
      (fun _ => []) (fun _ => some .I32) id := by
  simp only [code.read_memory_size,code.read_bulk_memory,code.require_memory,alloc.vec.Vec.is_empty,metadataOperands,Simd.readFixed,Std.bind_assoc]
  repeat' first
    | rfl
    | (split <;> simp_all)
    | (congr 1
       funext pair
       obtain ⟨res,state⟩ := pair
       cases res <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
         core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
         Std.bind_assoc,Std.uncurry])

theorem memory_grow_fixed (st : code.OpIterState) (data : Slice U8) (env : module.Env) :
    code.read_memory_grow st data env = metadataOperands (code.read_bulk_memory st data env)
      (fun _ => [.I32]) (fun _ => some .I32) id := by
  simp only [code.read_memory_grow,code.read_bulk_memory,code.require_memory,alloc.vec.Vec.is_empty,metadataOperands,Simd.readFixed,Std.bind_assoc]
  repeat' first
    | rfl
    | (split <;> simp_all)
    | (congr 1
       funext pair
       obtain ⟨res,state⟩ := pair
       cases res <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
         core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
         Std.bind_assoc,Std.uncurry])

theorem reader_memory_size_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st)
    (byte : data.val[p.start.val]'p.inbounds = 63#u8)
    (size : st.core.vals.val.length < Usize.max) (out : code.OpIterState)
    (accepted : code.read_memory_size st.core data env = .ok (.Ok (),out)) :
    MetadataReaderPost p (code.read_bulk_memory st.core data env) (fun _ => [])
      (fun _ => some .I32) id (fun _ => .MEMORY_SIZE) () out := by
  rw [memory_size_fixed] at accepted
  apply reader_metadata_wasm2 p (code.read_bulk_memory st.core data env) (fun _ => [])
    (fun _ => some .I32) id (fun _ => .MEMORY_SIZE) ?_ ?_ ?_ ?_ size () out accepted
  · apply WP.spec_mono (code.read_bulk_memory.spec st.core data env)
    rintro ⟨result,middle⟩ ⟨values,controls,decoded⟩
    refine ⟨values,controls,?_⟩
    intro unit success
    cases unit
    exact .plain (.of_immediate p.inbounds byte p.pos .memorySize (decoded success).1)
  · exact fun _ => .instr_case_62
  · rintro unit ⟨middle,read⟩ C matched
    cases unit
    have checked := code.read_bulk_memory.spec st.core data env
    rw [read,WP.spec_ok] at checked
    simpa [Simd.inputTypes,Simd.outputTypes,Translate.valueType] using matched.memory_size (checked.2.2 rfl).2
  · intro _ _
    simp [DeclaredReferences.Instruction,DeclaredReferences.instructionIndices]

theorem reader_memory_grow_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st)
    (byte : data.val[p.start.val]'p.inbounds = 64#u8)
    (size : st.core.vals.val.length < Usize.max) (out : code.OpIterState)
    (accepted : code.read_memory_grow st.core data env = .ok (.Ok (),out)) :
    MetadataReaderPost p (code.read_bulk_memory st.core data env) (fun _ => [.I32])
      (fun _ => some .I32) id (fun _ => .MEMORY_GROW) () out := by
  rw [memory_grow_fixed] at accepted
  apply reader_metadata_wasm2 p (code.read_bulk_memory st.core data env) (fun _ => [.I32])
    (fun _ => some .I32) id (fun _ => .MEMORY_GROW) ?_ ?_ ?_ ?_ size () out accepted
  · apply WP.spec_mono (code.read_bulk_memory.spec st.core data env)
    rintro ⟨result,middle⟩ ⟨values,controls,decoded⟩
    refine ⟨values,controls,?_⟩
    intro unit success
    cases unit
    exact .plain (.of_immediate p.inbounds byte p.pos .memoryGrow (decoded success).1)
  · exact fun _ => .instr_case_63
  · rintro unit ⟨middle,read⟩ C matched
    cases unit
    have checked := code.read_bulk_memory.spec st.core data env
    rw [read,WP.spec_ok] at checked
    simpa [Simd.inputTypes,Simd.outputTypes,Translate.valueType] using matched.memory_grow (checked.2.2 rfl).2
  · intro _ _
    simp [DeclaredReferences.Instruction,DeclaredReferences.instructionIndices]

end Itasca.Runtime.Compiler

end

/-! ## Stateful Reader Metadata Posts -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2

theorem reader_table_get_post_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 37#u8)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.read_table_get st.core data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out (.tableGet value.val) := by
  apply (reader_table_get_wasm2 p hbyte hsize value out accepted).stateful_post (.tableGet value.val) ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [SourceMachine.Stateful.Instruction.source,equality]

theorem reader_table_set_post_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 38#u8)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.read_table_set st.core data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out (.tableSet value.val) := by
  apply (reader_table_set_wasm2 p hbyte hsize value out accepted).stateful_post (.tableSet value.val) ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [SourceMachine.Stateful.Instruction.source,equality]

theorem reader_ref_null_post_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 208#u8)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : types.ElemType) (out : code.OpIterState)
    (accepted : code.read_ref_null st.core data = .ok (.Ok value,out)) :
    StatefulReaderPost p out (.refNull (Translate.referenceType value)) := by
  apply (reader_ref_null_wasm2 p hbyte hsize value out accepted).stateful_post (.refNull (Translate.referenceType value)) ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [SourceMachine.Stateful.Instruction.source,equality]

theorem reader_table_grow_post_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 15#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.read_table_grow {st.core with pos := next} data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out (.tableGrow value.val) := by
  apply (reader_table_grow_wasm2 p hbyte next hprefix hsize value out accepted).stateful_post (.tableGrow value.val) ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [SourceMachine.Stateful.Instruction.source,equality]

theorem reader_table_size_post_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 16#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.read_table_size {st.core with pos := next} data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out (.tableSize value.val) := by
  apply (reader_table_size_wasm2 p hbyte next hprefix hsize value out accepted).stateful_post (.tableSize value.val) ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [SourceMachine.Stateful.Instruction.source,equality]

theorem reader_table_fill_post_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 17#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.read_table_fill {st.core with pos := next} data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out (.tableFill value.val) := by
  apply (reader_table_fill_wasm2 p hbyte next hprefix hsize value out accepted).stateful_post (.tableFill value.val) ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [SourceMachine.Stateful.Instruction.source,equality]

theorem reader_data_drop_post_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 9#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.take_data_index {st.core with pos := next} data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out (.dataDrop value.val) := by
  apply (reader_data_drop_wasm2 p hbyte next hprefix hsize value out accepted).stateful_post (.dataDrop value.val) ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [SourceMachine.Stateful.Instruction.source,equality]

theorem reader_elem_drop_post_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 13#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32 × types.ValueType) (out : code.OpIterState)
    (accepted : code.take_element {st.core with pos := next} data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out (.elemDrop value.1.val) := by
  apply (reader_elem_drop_wasm2 p hbyte next hprefix hsize value out accepted).stateful_post (.elemDrop value.1.val) ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [SourceMachine.Stateful.Instruction.source,equality]

theorem reader_memory_fill_post_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 11#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : Unit) (out : code.OpIterState)
    (accepted : code.read_memory_fill {st.core with pos := next} data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out .memoryFill := by
  apply (reader_memory_fill_wasm2 p hbyte next hprefix hsize value out accepted).stateful_post .memoryFill ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [SourceMachine.Stateful.Instruction.source,equality]

theorem reader_memory_copy_post_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 10#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : Unit) (out : code.OpIterState)
    (accepted : code.read_memory_copy {st.core with pos := next} data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out .memoryCopy := by
  apply (reader_memory_copy_wasm2 p hbyte next hprefix hsize value out accepted).stateful_post .memoryCopy ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [SourceMachine.Stateful.Instruction.source,equality]

theorem reader_memory_init_post_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 8#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.read_memory_init {st.core with pos := next} data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out (.memoryInit value.val) := by
  apply (reader_memory_init_wasm2 p hbyte next hprefix hsize value out accepted).stateful_post (.memoryInit value.val) ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [SourceMachine.Stateful.Instruction.source,equality]

theorem reader_table_init_post_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 12#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32 × U32) (out : code.OpIterState)
    (accepted : code.read_table_init {st.core with pos := next} data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out (.tableInit value.2.val value.1.val) := by
  apply (reader_table_init_wasm2 p hbyte next hprefix hsize value out accepted).stateful_post (.tableInit value.2.val value.1.val) ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [SourceMachine.Stateful.Instruction.source,equality]

theorem reader_table_copy_post_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 14#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32 × U32) (out : code.OpIterState)
    (accepted : code.read_table_copy {st.core with pos := next} data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out (.tableCopy value.1.val value.2.val) := by
  apply (reader_table_copy_wasm2 p hbyte next hprefix hsize value out accepted).stateful_post (.tableCopy value.1.val value.2.val) ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [SourceMachine.Stateful.Instruction.source,equality]

theorem reader_memory_size_post_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st)
    (byte : data.val[p.start.val]'p.inbounds = 63#u8)
    (size : st.core.vals.val.length < Usize.max) (out : code.OpIterState)
    (accepted : code.read_memory_size st.core data env = .ok (.Ok (),out)) :
    StatefulReaderPost p out .memorySize := by
  apply (reader_memory_size_wasm2 p byte size out accepted).stateful_post .memorySize ?_ size
  intro a equality
  try dsimp only [id] at equality
  simp only [SourceMachine.Stateful.Instruction.source,equality]

theorem reader_memory_grow_post_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st)
    (byte : data.val[p.start.val]'p.inbounds = 64#u8)
    (size : st.core.vals.val.length < Usize.max) (out : code.OpIterState)
    (accepted : code.read_memory_grow st.core data env = .ok (.Ok (),out)) :
    StatefulReaderPost p out .memoryGrow := by
  apply (reader_memory_grow_wasm2 p byte size out accepted).stateful_post .memoryGrow ?_ size
  intro a equality
  try dsimp only [id] at equality
  simp only [SourceMachine.Stateful.Instruction.source,equality]

end Itasca.Runtime.Compiler

end
