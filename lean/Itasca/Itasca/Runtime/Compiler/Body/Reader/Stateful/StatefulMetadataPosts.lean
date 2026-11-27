import Itasca.Runtime.Compiler.Body.Reader.Replay.MetadataTypes
import Itasca.Runtime.SourceMachine.Stateful.AccessAndGrowth
import Itasca.Body.References.Reader
import Itasca.Runtime.Compiler.Body.Reader.Replay.Post
import Itasca.Body.Bulk.Step

open WebAssembly

/-!
Proofs for Runtime / Compiler / Body / Reader / Stateful.

This module collects StatefulPost, StatefulMetadataPosts.
Each section documents its contracts and consumers.
-/

/-! ## StatefulPost -/

section

/-!
A stateful source reader advances the exact supplied zipper in all paths; live concrete operands additionally expose its context-derived signature.

Main declarations: `StatefulReaderPost`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Body

/-- A stateful source reader advances the exact supplied zipper in all paths;
live concrete operands additionally expose its context-derived signature. -/
def StatefulReaderPost {data env locals index st}
    (p : Pending data env locals index st) (out : code.OpIterState) (op : SourceMachine.Stateful.Instruction) : Prop :=
  ∃ values, Body.ReaderPost p out op.source p.current.ctrl.polymorphic_base values ∧
    ∀ C, Translation.Environment.Matches env ⟨locals,p.ft.results⟩ C →
      ConcreteStack st.core.vals.val → p.current.ctrl.polymorphic_base = false →
      ∃ front input output, SourceMachine.Stateful.Signature C op input output ∧
        Body.Stack.stackTypes st.core.vals.val = front ++ input ∧
        Body.Stack.stackTypes out.vals.val = front ++ output ∧ ConcreteStack out.vals.val

theorem _root_.Itasca.Body.MetadataReaderPost.stateful_post {data env locals index st}
    {p : Pending data env locals index st} {D M : Type}
    {decode : Result (core.result.Result D error.OpError × code.OpIterState)}
    {pops : D → List wasm_types.ValueType} {output : D → Option wasm_types.ValueType}
    {metadata : D → M} {operation : D → instr} {value : M} {out : code.OpIterState}
    (post : Body.MetadataReaderPost p decode pops output metadata operation value out)
    (op : SourceMachine.Stateful.Instruction)
    (source : ∀ a, metadata a = value → operation a = op.source)
    (size : st.core.vals.val.length < Usize.max) : StatefulReaderPost p out op := by
  obtain ⟨a,middle,values,decoded,middleValues,middleControls,metadataEq,read,controls,position,effect,sourcePost,principal⟩ := post
  refine ⟨values,by simpa only [source a metadataEq] using sourcePost,?_⟩
  intro C matched known monomorphic
  have retained : Body.MetadataReaderPost p decode pops output metadata operation value out :=
    ⟨a,middle,values,decoded,middleValues,middleControls,metadataEq,read,controls,position,effect,sourcePost,principal⟩
  obtain ⟨b,metadataEq,front,beforeTypes,afterTypes,afterKnown,typed,_,_⟩ := retained.types known monomorphic size
  refine ⟨front,Simd.inputTypes (pops b),Simd.outputTypes (output b),?_,beforeTypes,afterTypes,afterKnown⟩
  exact SourceMachine.Stateful.Signature.of_typed (by simpa only [source b metadataEq] using typed C matched)

end Itasca.Compiler

end

/-! ## StatefulMetadataPosts -/

section

/-!
Stateful reader postconditions for reference, memory/table and segment operations. Per-opcode reader effects establish the shared stateful metadata certificates.
-/

/-! ## Reader Stateful Bulk -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Body

theorem reader_memory_fill {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 11#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : Unit) (out : code.OpIterState)
    (accepted : code.read_memory_fill {st.core with pos := next} data env = .ok (.Ok value,out)) :
    Body.MetadataReaderPost p (code.read_bulk_memory {st.core with pos := next} data env) (fun _ => [.I32,.I32,.I32]) (fun _ => none) id
      (fun _ => .MEMORY_FILL) value out := by
  rw [code.read_memory_fill.fixed] at accepted
  apply Body.Pending.metadata_reader_accepted p (code.read_bulk_memory {st.core with pos := next} data env) (fun _ => [.I32,.I32,.I32]) (fun _ => none) id
    (fun _ => .MEMORY_FILL) ?_ ?_ ?_ ?_ hsize value out accepted
  · apply WP.spec_mono (code.read_bulk_memory.spec {st.core with pos := next} data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    refine ⟨hv, hc, ?_⟩
    intro u hok
    cases u
    obtain ⟨hb, _⟩ := hd hok
    obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
    exact At.of_immediate p.inbounds hbyte p.pos (.bulk 11#u32 hpe .memoryFill)
      ((Body.Scalar.BytesAt.mk hp hpl hpb).append hb)
  · exact fun _ => .instr_case_64
  · rintro u ⟨decoded, hrun⟩ C hC
    cases u
    have hspec := code.read_bulk_memory.spec {st.core with pos := next} data env
    rw [hrun, WP.spec_ok] at hspec
    simpa [Simd.inputTypes, Simd.outputTypes, Translation.valueType] using hC.memory_fill (hspec.2.2 rfl).2
  · intro a _
    simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]

theorem reader_memory_copy {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 10#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : Unit) (out : code.OpIterState)
    (accepted : code.read_memory_copy {st.core with pos := next} data env = .ok (.Ok value,out)) :
    Body.MetadataReaderPost p (memoryCopyMetadata {st.core with pos := next} data env) (fun _ => [.I32,.I32,.I32]) (fun _ => none) id
      (fun _ => .MEMORY_COPY) value out := by
  rw [code.read_memory_copy.fixed] at accepted
  apply Body.Pending.metadata_reader_accepted p (memoryCopyMetadata {st.core with pos := next} data env) (fun _ => [.I32,.I32,.I32]) (fun _ => none) id
    (fun _ => .MEMORY_COPY) ?_ ?_ ?_ ?_ hsize value out accepted
  · apply WP.spec_mono (memoryCopyMetadata.spec {st.core with pos := next} data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    refine ⟨hv, hc, ?_⟩
    intro u hok
    cases u
    obtain ⟨hb, _⟩ := hd hok
    obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
    exact At.of_immediate p.inbounds hbyte p.pos (.bulk 10#u32 hpe .memoryCopy)
      ((Body.Scalar.BytesAt.mk hp hpl hpb).append hb)
  · exact fun _ => .instr_case_65
  · rintro u ⟨decoded, hrun⟩ C hC
    cases u
    have hspec := memoryCopyMetadata.spec {st.core with pos := next} data env
    rw [hrun, WP.spec_ok] at hspec
    simpa [Simd.inputTypes, Simd.outputTypes, Translation.valueType] using hC.memory_copy (hspec.2.2 rfl).2
  · intro a _
    simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]

theorem reader_memory_init {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 8#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.read_memory_init {st.core with pos := next} data env = .ok (.Ok value,out)) :
    Body.MetadataReaderPost p (memoryInitMetadata {st.core with pos := next} data env) (fun _ => [.I32,.I32,.I32]) (fun _ => none) id
      (fun idx => .MEMORY_INIT (.mk_uN idx.val)) value out := by
  rw [code.read_memory_init.fixed] at accepted
  apply Body.Pending.metadata_reader_accepted p (memoryInitMetadata {st.core with pos := next} data env) (fun _ => [.I32,.I32,.I32]) (fun _ => none) id
    (fun idx => .MEMORY_INIT (.mk_uN idx.val)) ?_ ?_ ?_ ?_ hsize value out accepted
  · apply WP.spec_mono (memoryInitMetadata.spec {st.core with pos := next} data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    refine ⟨hv, hc, ?_⟩
    intro idx hok
    obtain ⟨bytes, hb, he, _⟩ := hd idx hok
    obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
    exact At.of_immediate p.inbounds hbyte p.pos (.bulk 8#u32 hpe (.memoryInit idx he))
      ((Body.Scalar.BytesAt.mk hp hpl hpb).append hb)
  · exact fun idx => .instr_case_66 _ (Translation.Environment.index_wf idx)
  · rintro idx ⟨decoded, hrun⟩ C hC
    have hspec := memoryInitMetadata.spec {st.core with pos := next} data env
    rw [hrun, WP.spec_ok] at hspec
    obtain ⟨_, _, _, ⟨count, hcount, hi⟩, hm⟩ := hspec.2.2 idx rfl
    simpa [Simd.inputTypes, Simd.outputTypes, Translation.valueType] using hC.memory_init idx count hcount hi hm
  · intro a _
    simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]

theorem reader_table_init {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 12#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32 × U32) (out : code.OpIterState)
    (accepted : code.read_table_init {st.core with pos := next} data env = .ok (.Ok value,out)) :
    Body.MetadataReaderPost p (referencePairMetadata (code.take_element {st.core with pos := next} data env) data env) (fun _ => [.I32,.I32,.I32]) (fun _ => none) id
      (fun a => .TABLE_INIT (.mk_uN a.2.val) (.mk_uN a.1.val)) value out := by
  rw [code.read_table_init.fixed] at accepted
  have hmetadata := referencePairMetadata.spec {st.core with pos := next} data env
    (code.take_element {st.core with pos := next} data env)
    (fun i ty pos => Binary.Leb128.Decoded data next i pos ∧
      ∃ hi : i.val < env.elements.val.length,
        ty = Module.Constants.referenceValueType env.elements.val[i.val].elem)
    (code.take_element.spec {st.core with pos := next} data env)
  apply Body.Pending.metadata_reader_accepted p (referencePairMetadata (code.take_element {st.core with pos := next} data env) data env) (fun _ => [.I32,.I32,.I32]) (fun _ => none) id
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
      ((Body.Scalar.BytesAt.mk hp hpl hpb).append ((Body.Scalar.BytesAt.mk his hil hib).append ⟨hjs, hjl, hjb⟩))
  · exact fun a => .instr_case_54 _ _ (Translation.Environment.index_wf a.2) (Translation.Environment.index_wf a.1)
  · rintro ⟨i, j⟩ ⟨decoded, hrun⟩ C hC
    rw [hrun, WP.spec_ok] at hmetadata
    obtain ⟨middle, ty, ⟨_, hi, hity⟩, _, hj, hjty⟩ := hmetadata.2.2 i j rfl
    simpa [Simd.inputTypes, Simd.outputTypes, Translation.valueType] using
      hC.table_init j i env.table_types.val[j.val] env.elements.val[i.val] hj hi rfl rfl (reference_value_injective (hity.symm.trans hjty))
  · intro a _
    simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]

theorem reader_table_copy {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 14#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32 × U32) (out : code.OpIterState)
    (accepted : code.read_table_copy {st.core with pos := next} data env = .ok (.Ok value,out)) :
    Body.MetadataReaderPost p (referencePairMetadata (code.take_table {st.core with pos := next} data env) data env) (fun _ => [.I32,.I32,.I32]) (fun _ => none) id
      (fun a => .TABLE_COPY (.mk_uN a.1.val) (.mk_uN a.2.val)) value out := by
  rw [code.read_table_copy.fixed] at accepted
  have hmetadata := referencePairMetadata.spec {st.core with pos := next} data env
    (code.take_table {st.core with pos := next} data env)
    (fun i ty pos => Binary.Leb128.Decoded data next i pos ∧
      ∃ hi : i.val < env.table_types.val.length,
        ty = Module.Constants.referenceValueType env.table_types.val[i.val].elem)
    (code.take_table.spec {st.core with pos := next} data env)
  apply Body.Pending.metadata_reader_accepted p (referencePairMetadata (code.take_table {st.core with pos := next} data env) data env) (fun _ => [.I32,.I32,.I32]) (fun _ => none) id
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
      ((Body.Scalar.BytesAt.mk hp hpl hpb).append ((Body.Scalar.BytesAt.mk his hil hib).append ⟨hjs, hjl, hjb⟩))
  · exact fun a => .instr_case_53 _ _ (Translation.Environment.index_wf a.1) (Translation.Environment.index_wf a.2)
  · rintro ⟨i, j⟩ ⟨decoded, hrun⟩ C hC
    rw [hrun, WP.spec_ok] at hmetadata
    obtain ⟨middle, ty, ⟨_, hi, hity⟩, _, hj, hjty⟩ := hmetadata.2.2 i j rfl
    simpa [Simd.inputTypes, Simd.outputTypes, Translation.valueType] using
      hC.table_copy i j env.table_types.val[i.val] env.table_types.val[j.val] hi hj rfl rfl (reference_value_injective (hjty.symm.trans hity))
  · intro a _
    simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]

end Itasca.Compiler

end

/-! ## Reader Stateful Metadata -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Body

theorem reader_table_get {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 37#u8)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.read_table_get st.core data env = .ok (.Ok value,out)) :
    Body.MetadataReaderPost p (code.take_table st.core data env) (fun _ => [.I32]) (fun a => some a.2) Prod.fst
      (fun a => .TABLE_GET (.mk_uN a.1.val)) value out := by
  rw [code.read_table_get.fixed] at accepted
  apply Body.Pending.metadata_reader_accepted p (code.take_table st.core data env) (fun _ => [.I32]) (fun a => some a.2) Prod.fst
    (fun a => .TABLE_GET (.mk_uN a.1.val)) ?_ ?_ ?_ ?_ hsize value out accepted
  · apply WP.spec_mono (code.take_table.spec st.core data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    dsimp only at hv hc hd ⊢
    refine ⟨hv, hc, ?_⟩
    rintro ⟨idx, ty⟩ hok
    obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := (hd idx ty hok).1
    exact At.of_immediate p.inbounds hbyte p.pos (.reference (.tableGet idx hencoding))
      ⟨hbytes, hlen, hbound⟩
  · exact fun a => .instr_case_48 _ (Translation.Environment.index_wf a.1)
  · rintro ⟨idx, ty⟩ ⟨decoded, hrun⟩ C hC
    have hspec := code.take_table.spec st.core data env
    rw [hrun, WP.spec_ok] at hspec
    obtain ⟨_, hi, hty⟩ := hspec.2.2 idx ty rfl
    have htyped := hC.table_get idx env.table_types.val[idx.val] hi rfl
    simpa [Simd.inputTypes, Simd.outputTypes, hty, reference_value_translation, show Translation.valueType .I32 = valtype.I32 from rfl]
      using htyped
  · intro a _
    simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]

theorem reader_table_set {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 38#u8)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.read_table_set st.core data env = .ok (.Ok value,out)) :
    Body.MetadataReaderPost p (code.take_table st.core data env) (fun a => [a.2, .I32]) (fun _ => none) Prod.fst
      (fun a => .TABLE_SET (.mk_uN a.1.val)) value out := by
  rw [code.read_table_set.fixed] at accepted
  apply Body.Pending.metadata_reader_accepted p (code.take_table st.core data env) (fun a => [a.2, .I32]) (fun _ => none) Prod.fst
    (fun a => .TABLE_SET (.mk_uN a.1.val)) ?_ ?_ ?_ ?_ hsize value out accepted
  · apply WP.spec_mono (code.take_table.spec st.core data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    dsimp only at hv hc hd ⊢
    refine ⟨hv, hc, ?_⟩
    rintro ⟨idx, ty⟩ hok
    obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := (hd idx ty hok).1
    exact At.of_immediate p.inbounds hbyte p.pos (.reference (.tableSet idx hencoding))
      ⟨hbytes, hlen, hbound⟩
  · exact fun a => .instr_case_49 _ (Translation.Environment.index_wf a.1)
  · rintro ⟨idx, ty⟩ ⟨decoded, hrun⟩ C hC
    have hspec := code.take_table.spec st.core data env
    rw [hrun, WP.spec_ok] at hspec
    obtain ⟨_, hi, hty⟩ := hspec.2.2 idx ty rfl
    have htyped := hC.table_set idx env.table_types.val[idx.val] hi rfl
    simpa [Simd.inputTypes, Simd.outputTypes, hty, reference_value_translation, show Translation.valueType .I32 = valtype.I32 from rfl]
      using htyped
  · intro a _
    simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]

theorem reader_ref_null {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 208#u8)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : wasm_types.ElemType) (out : code.OpIterState)
    (accepted : code.read_ref_null st.core data = .ok (.Ok value,out)) :
    Body.MetadataReaderPost p (code.take_reference_type st.core data) (fun _ => []) (fun rt => some (Module.Constants.referenceValueType rt)) id
      (fun rt => .REF_NULL (Translation.referenceType rt)) value out := by
  rw [code.read_ref_null.fixed] at accepted
  apply Body.Pending.metadata_reader_accepted p (code.take_reference_type st.core data) (fun _ => []) (fun rt => some (Module.Constants.referenceValueType rt)) id
    (fun rt => .REF_NULL (Translation.referenceType rt)) ?_ ?_ ?_ ?_ hsize value out accepted
  · apply WP.spec_mono (code.take_reference_type.spec st.core data)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    exact ⟨hv, hc, fun rt hok => At.of_immediate p.inbounds hbyte p.pos
      (.reference (.refNull rt)) (hd rt hok)⟩
  · exact fun _ => .instr_case_40 _
  · intro rt _ C hC
    simpa [Simd.inputTypes, Simd.outputTypes, reference_value_translation] using
      Instr_ok.ref_null C (Translation.referenceType rt) hC.wf (.instr_case_40 _)

  · intro a _
    simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]

theorem reader_table_grow {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 15#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.read_table_grow {st.core with pos := next} data env = .ok (.Ok value,out)) :
    Body.MetadataReaderPost p (code.take_table {st.core with pos := next} data env) (fun a => [.I32, a.2]) (fun _ => some .I32) Prod.fst
      (fun a => .TABLE_GROW (.mk_uN a.1.val)) value out := by
  rw [code.read_table_grow.fixed] at accepted
  apply Body.Pending.metadata_reader_accepted p (code.take_table {st.core with pos := next} data env) (fun a => [.I32, a.2]) (fun _ => some .I32) Prod.fst
    (fun a => .TABLE_GROW (.mk_uN a.1.val)) ?_ ?_ ?_ ?_ hsize value out accepted
  · apply WP.spec_mono (code.take_table.spec {st.core with pos := next} data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    dsimp only at hv hc hd ⊢
    refine ⟨hv, hc, ?_⟩
    rintro ⟨idx, ty⟩ hok
    obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := (hd idx ty hok).1
    obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
    exact At.of_immediate p.inbounds hbyte p.pos (.bulk 15#u32 hpe (.tableGrow idx hencoding))
      ((Body.Scalar.BytesAt.mk hp hpl hpb).append ⟨hbytes, hlen, hbound⟩)
  · exact fun a => .instr_case_51 _ (Translation.Environment.index_wf a.1)
  · rintro ⟨idx, ty⟩ ⟨decoded, hrun⟩ C hC
    have hspec := code.take_table.spec {st.core with pos := next} data env
    rw [hrun, WP.spec_ok] at hspec
    obtain ⟨_, hi, hty⟩ := hspec.2.2 idx ty rfl
    have htyped := hC.table_grow idx env.table_types.val[idx.val] hi rfl
    simpa [Simd.inputTypes, Simd.outputTypes, hty, reference_value_translation,
      show Translation.valueType .I32 = valtype.I32 from rfl] using htyped
  · intro a _
    simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]

theorem reader_table_size {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 16#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.read_table_size {st.core with pos := next} data env = .ok (.Ok value,out)) :
    Body.MetadataReaderPost p (code.take_table {st.core with pos := next} data env) (fun _ => []) (fun _ => some .I32) Prod.fst
      (fun a => .TABLE_SIZE (.mk_uN a.1.val)) value out := by
  rw [code.read_table_size.fixed] at accepted
  apply Body.Pending.metadata_reader_accepted p (code.take_table {st.core with pos := next} data env) (fun _ => []) (fun _ => some .I32) Prod.fst
    (fun a => .TABLE_SIZE (.mk_uN a.1.val)) ?_ ?_ ?_ ?_ hsize value out accepted
  · apply WP.spec_mono (code.take_table.spec {st.core with pos := next} data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    dsimp only at hv hc hd ⊢
    refine ⟨hv, hc, ?_⟩
    rintro ⟨idx, ty⟩ hok
    obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := (hd idx ty hok).1
    obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
    exact At.of_immediate p.inbounds hbyte p.pos (.bulk 16#u32 hpe (.tableSize idx hencoding))
      ((Body.Scalar.BytesAt.mk hp hpl hpb).append ⟨hbytes, hlen, hbound⟩)
  · exact fun a => .instr_case_50 _ (Translation.Environment.index_wf a.1)
  · rintro ⟨idx, ty⟩ ⟨decoded, hrun⟩ C hC
    have hspec := code.take_table.spec {st.core with pos := next} data env
    rw [hrun, WP.spec_ok] at hspec
    obtain ⟨_, hi, hty⟩ := hspec.2.2 idx ty rfl
    have htyped := hC.table_size idx env.table_types.val[idx.val] hi rfl
    simpa [Simd.inputTypes, Simd.outputTypes, hty, reference_value_translation,
      show Translation.valueType .I32 = valtype.I32 from rfl] using htyped
  · intro a _
    simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]

theorem reader_table_fill {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 17#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.read_table_fill {st.core with pos := next} data env = .ok (.Ok value,out)) :
    Body.MetadataReaderPost p (code.take_table {st.core with pos := next} data env) (fun a => [.I32, a.2, .I32]) (fun _ => none) Prod.fst
      (fun a => .TABLE_FILL (.mk_uN a.1.val)) value out := by
  rw [code.read_table_fill.fixed] at accepted
  apply Body.Pending.metadata_reader_accepted p (code.take_table {st.core with pos := next} data env) (fun a => [.I32, a.2, .I32]) (fun _ => none) Prod.fst
    (fun a => .TABLE_FILL (.mk_uN a.1.val)) ?_ ?_ ?_ ?_ hsize value out accepted
  · apply WP.spec_mono (code.take_table.spec {st.core with pos := next} data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    dsimp only at hv hc hd ⊢
    refine ⟨hv, hc, ?_⟩
    rintro ⟨idx, ty⟩ hok
    obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := (hd idx ty hok).1
    obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
    exact At.of_immediate p.inbounds hbyte p.pos (.bulk 17#u32 hpe (.tableFill idx hencoding))
      ((Body.Scalar.BytesAt.mk hp hpl hpb).append ⟨hbytes, hlen, hbound⟩)
  · exact fun a => .instr_case_52 _ (Translation.Environment.index_wf a.1)
  · rintro ⟨idx, ty⟩ ⟨decoded, hrun⟩ C hC
    have hspec := code.take_table.spec {st.core with pos := next} data env
    rw [hrun, WP.spec_ok] at hspec
    obtain ⟨_, hi, hty⟩ := hspec.2.2 idx ty rfl
    have htyped := hC.table_fill idx env.table_types.val[idx.val] hi rfl
    simpa [Simd.inputTypes, Simd.outputTypes, hty, reference_value_translation,
      show Translation.valueType .I32 = valtype.I32 from rfl] using htyped
  · intro a _
    simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]

theorem reader_data_drop {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 9#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.take_data_index {st.core with pos := next} data env = .ok (.Ok value,out)) :
    Body.MetadataReaderPost p (code.take_data_index {st.core with pos := next} data env) (fun _ => []) (fun _ => none) id
      (fun idx => .DATA_DROP (.mk_uN idx.val)) value out := by
  rw [← metadataOperands.empty (code.take_data_index {st.core with pos := next} data env)] at accepted
  apply Body.Pending.metadata_reader_accepted p (code.take_data_index {st.core with pos := next} data env) (fun _ => []) (fun _ => none) id
    (fun idx => .DATA_DROP (.mk_uN idx.val)) ?_ ?_ ?_ ?_ hsize value out accepted
  · apply WP.spec_mono (code.take_data_index.spec {st.core with pos := next} data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    refine ⟨hv, hc, ?_⟩
    intro idx hok
    obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := (hd idx hok).1
    obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
    exact At.of_immediate p.inbounds hbyte p.pos (.bulk 9#u32 hpe (.dataDrop idx hencoding))
      ((Body.Scalar.BytesAt.mk hp hpl hpb).append ⟨hbytes, hlen, hbound⟩)
  · exact fun a => .instr_case_67 _ (Translation.Environment.index_wf a)
  · rintro idx ⟨decoded, hrun⟩ C hC
    have hspec := code.take_data_index.spec {st.core with pos := next} data env
    rw [hrun, WP.spec_ok] at hspec
    obtain ⟨_, count, hc, hi⟩ := hspec.2.2 idx rfl
    exact hC.data_drop idx count hc hi
  · intro a _
    simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]

theorem reader_elem_drop {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 13#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32 × wasm_types.ValueType) (out : code.OpIterState)
    (accepted : code.take_element {st.core with pos := next} data env = .ok (.Ok value,out)) :
    Body.MetadataReaderPost p (code.take_element {st.core with pos := next} data env) (fun _ => []) (fun _ => none) id
      (fun a => .ELEM_DROP (.mk_uN a.1.val)) value out := by
  rw [← metadataOperands.empty (code.take_element {st.core with pos := next} data env)] at accepted
  apply Body.Pending.metadata_reader_accepted p (code.take_element {st.core with pos := next} data env) (fun _ => []) (fun _ => none) id
    (fun a => .ELEM_DROP (.mk_uN a.1.val)) ?_ ?_ ?_ ?_ hsize value out accepted
  · apply WP.spec_mono (code.take_element.spec {st.core with pos := next} data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    refine ⟨hv, hc, ?_⟩
    rintro ⟨idx, ty⟩ hok
    obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := (hd idx ty hok).1
    obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
    exact At.of_immediate p.inbounds hbyte p.pos (.bulk 13#u32 hpe (.elemDrop idx hencoding))
      ((Body.Scalar.BytesAt.mk hp hpl hpb).append ⟨hbytes, hlen, hbound⟩)
  · exact fun a => .instr_case_55 _ (Translation.Environment.index_wf a.1)
  · rintro ⟨idx, ty⟩ ⟨decoded, hrun⟩ C hC
    have hspec := code.take_element.spec {st.core with pos := next} data env
    rw [hrun, WP.spec_ok] at hspec
    obtain ⟨_, hi, hty⟩ := hspec.2.2 idx ty rfl
    exact hC.elem_drop idx env.elements.val[idx.val] hi rfl
  · intro a _
    simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]

end Itasca.Compiler

end

/-! ## Reader Memory Metadata -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Body

theorem memory_size_fixed (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) :
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

theorem memory_grow_fixed (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) :
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

theorem reader_memory_size {data env locals index st}
    (p : Pending data env locals index st)
    (byte : data.val[p.start.val]'p.inbounds = 63#u8)
    (size : st.core.vals.val.length < Usize.max) (out : code.OpIterState)
    (accepted : code.read_memory_size st.core data env = .ok (.Ok (),out)) :
    Body.MetadataReaderPost p (code.read_bulk_memory st.core data env) (fun _ => [])
      (fun _ => some .I32) id (fun _ => .MEMORY_SIZE) () out := by
  rw [memory_size_fixed] at accepted
  apply Body.Pending.metadata_reader_accepted p (code.read_bulk_memory st.core data env) (fun _ => [])
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
    simpa [Simd.inputTypes,Simd.outputTypes,Translation.valueType] using matched.memory_size (checked.2.2 rfl).2
  · intro _ _
    simp [Spec.DeclaredReferences.Instruction,Spec.DeclaredReferences.instructionIndices]

theorem reader_memory_grow {data env locals index st}
    (p : Pending data env locals index st)
    (byte : data.val[p.start.val]'p.inbounds = 64#u8)
    (size : st.core.vals.val.length < Usize.max) (out : code.OpIterState)
    (accepted : code.read_memory_grow st.core data env = .ok (.Ok (),out)) :
    Body.MetadataReaderPost p (code.read_bulk_memory st.core data env) (fun _ => [.I32])
      (fun _ => some .I32) id (fun _ => .MEMORY_GROW) () out := by
  rw [memory_grow_fixed] at accepted
  apply Body.Pending.metadata_reader_accepted p (code.read_bulk_memory st.core data env) (fun _ => [.I32])
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
    simpa [Simd.inputTypes,Simd.outputTypes,Translation.valueType] using matched.memory_grow (checked.2.2 rfl).2
  · intro _ _
    simp [Spec.DeclaredReferences.Instruction,Spec.DeclaredReferences.instructionIndices]

end Itasca.Compiler

end

/-! ## Stateful Reader Metadata Posts -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Body

theorem reader_table_get_post {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 37#u8)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.read_table_get st.core data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out (.tableGet value.val) := by
  apply (reader_table_get p hbyte hsize value out accepted).stateful_post (.tableGet value.val) ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [SourceMachine.Stateful.Instruction.source,equality]

theorem reader_table_set_post {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 38#u8)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.read_table_set st.core data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out (.tableSet value.val) := by
  apply (reader_table_set p hbyte hsize value out accepted).stateful_post (.tableSet value.val) ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [SourceMachine.Stateful.Instruction.source,equality]

theorem reader_ref_null_post {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 208#u8)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : wasm_types.ElemType) (out : code.OpIterState)
    (accepted : code.read_ref_null st.core data = .ok (.Ok value,out)) :
    StatefulReaderPost p out (.refNull (Translation.referenceType value)) := by
  apply (reader_ref_null p hbyte hsize value out accepted).stateful_post (.refNull (Translation.referenceType value)) ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [SourceMachine.Stateful.Instruction.source,equality]

theorem reader_table_grow_post {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 15#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.read_table_grow {st.core with pos := next} data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out (.tableGrow value.val) := by
  apply (reader_table_grow p hbyte next hprefix hsize value out accepted).stateful_post (.tableGrow value.val) ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [SourceMachine.Stateful.Instruction.source,equality]

theorem reader_table_size_post {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 16#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.read_table_size {st.core with pos := next} data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out (.tableSize value.val) := by
  apply (reader_table_size p hbyte next hprefix hsize value out accepted).stateful_post (.tableSize value.val) ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [SourceMachine.Stateful.Instruction.source,equality]

theorem reader_table_fill_post {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 17#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.read_table_fill {st.core with pos := next} data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out (.tableFill value.val) := by
  apply (reader_table_fill p hbyte next hprefix hsize value out accepted).stateful_post (.tableFill value.val) ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [SourceMachine.Stateful.Instruction.source,equality]

theorem reader_data_drop_post {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 9#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.take_data_index {st.core with pos := next} data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out (.dataDrop value.val) := by
  apply (reader_data_drop p hbyte next hprefix hsize value out accepted).stateful_post (.dataDrop value.val) ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [SourceMachine.Stateful.Instruction.source,equality]

theorem reader_elem_drop_post {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 13#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32 × wasm_types.ValueType) (out : code.OpIterState)
    (accepted : code.take_element {st.core with pos := next} data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out (.elemDrop value.1.val) := by
  apply (reader_elem_drop p hbyte next hprefix hsize value out accepted).stateful_post (.elemDrop value.1.val) ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [SourceMachine.Stateful.Instruction.source,equality]

theorem reader_memory_fill_post {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 11#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : Unit) (out : code.OpIterState)
    (accepted : code.read_memory_fill {st.core with pos := next} data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out .memoryFill := by
  apply (reader_memory_fill p hbyte next hprefix hsize value out accepted).stateful_post .memoryFill ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [SourceMachine.Stateful.Instruction.source,equality]

theorem reader_memory_copy_post {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 10#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : Unit) (out : code.OpIterState)
    (accepted : code.read_memory_copy {st.core with pos := next} data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out .memoryCopy := by
  apply (reader_memory_copy p hbyte next hprefix hsize value out accepted).stateful_post .memoryCopy ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [SourceMachine.Stateful.Instruction.source,equality]

theorem reader_memory_init_post {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 8#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.read_memory_init {st.core with pos := next} data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out (.memoryInit value.val) := by
  apply (reader_memory_init p hbyte next hprefix hsize value out accepted).stateful_post (.memoryInit value.val) ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [SourceMachine.Stateful.Instruction.source,equality]

theorem reader_table_init_post {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 12#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32 × U32) (out : code.OpIterState)
    (accepted : code.read_table_init {st.core with pos := next} data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out (.tableInit value.2.val value.1.val) := by
  apply (reader_table_init p hbyte next hprefix hsize value out accepted).stateful_post (.tableInit value.2.val value.1.val) ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [SourceMachine.Stateful.Instruction.source,equality]

theorem reader_table_copy_post {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 14#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32 × U32) (out : code.OpIterState)
    (accepted : code.read_table_copy {st.core with pos := next} data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out (.tableCopy value.1.val value.2.val) := by
  apply (reader_table_copy p hbyte next hprefix hsize value out accepted).stateful_post (.tableCopy value.1.val value.2.val) ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [SourceMachine.Stateful.Instruction.source,equality]

theorem reader_memory_size_post {data env locals index st}
    (p : Pending data env locals index st)
    (byte : data.val[p.start.val]'p.inbounds = 63#u8)
    (size : st.core.vals.val.length < Usize.max) (out : code.OpIterState)
    (accepted : code.read_memory_size st.core data env = .ok (.Ok (),out)) :
    StatefulReaderPost p out .memorySize := by
  apply (reader_memory_size p byte size out accepted).stateful_post .memorySize ?_ size
  intro a equality
  try dsimp only [id] at equality
  simp only [SourceMachine.Stateful.Instruction.source,equality]

theorem reader_memory_grow_post {data env locals index st}
    (p : Pending data env locals index st)
    (byte : data.val[p.start.val]'p.inbounds = 64#u8)
    (size : st.core.vals.val.length < Usize.max) (out : code.OpIterState)
    (accepted : code.read_memory_grow st.core data env = .ok (.Ok (),out)) :
    StatefulReaderPost p out .memoryGrow := by
  apply (reader_memory_grow p byte size out accepted).stateful_post .memoryGrow ?_ size
  intro a equality
  try dsimp only [id] at equality
  simp only [SourceMachine.Stateful.Instruction.source,equality]

end Itasca.Compiler

end

end
