import Exec.Code.Body.Reader.Common.ReaderMetadata
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2

theorem reader_table_get_wasm2 {data env locals index st} (p : Pending data env locals index st)
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

theorem reader_table_set_wasm2 {data env locals index st} (p : Pending data env locals index st)
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

theorem reader_ref_null_wasm2 {data env locals index st} (p : Pending data env locals index st)
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

theorem reader_table_grow_wasm2 {data env locals index st} (p : Pending data env locals index st)
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

theorem reader_table_size_wasm2 {data env locals index st} (p : Pending data env locals index st)
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

theorem reader_table_fill_wasm2 {data env locals index st} (p : Pending data env locals index st)
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

theorem reader_data_drop_wasm2 {data env locals index st} (p : Pending data env locals index st)
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

theorem reader_elem_drop_wasm2 {data env locals index st} (p : Pending data env locals index st)
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

end Exec.Code
