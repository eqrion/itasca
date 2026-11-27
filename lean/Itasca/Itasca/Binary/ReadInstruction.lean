import Itasca.Binary.ReaderBytes

namespace Itasca.Binary.Source
open Aeneas.Std WebAssembly

private theorem indices {xs bs} (h : WebAssembly.Binary.Scalar.IndicesEncoding xs bs) :
    ∃ ys : List U32, ys.map UScalar.val = xs ∧ Body.Scalar.IndicesEncoding ys (readerBytes bs) := by
  induction h with
  | nil => exact ⟨[], rfl, .nil⟩
  | cons hx _ ih =>
    obtain ⟨i, rfl, hi⟩ := readerIndex hx
    obtain ⟨ys, rfl, hy⟩ := ih
    exact ⟨i :: ys, rfl, by simp only [readerBytes, List.map_append]; exact .cons hi hy⟩

private theorem memory {opcode operation} (arg : code.MemArg)
    (h : WebAssembly.Binary.MemoryMeaning.opcodeMeaning opcode = some operation) :
    ∃ row, Body.MemoryMeaning.opcodeMeaning (readerByte opcode) = some row ∧
      row.op arg = operation.op (Body.MemoryMeaning.memArg arg) := by
  unfold WebAssembly.Binary.MemoryMeaning.opcodeMeaning WebAssembly.Binary.MemoryMeaning.opcodeTable at h
  unfold Body.MemoryMeaning.opcodeMeaning
  rw [show (readerByte opcode).val = opcode.toNat from rfl]
  split at h <;> try contradiction
  all_goals cases h; exact ⟨_, rfl, rfl⟩

private theorem scalar {oc op bs} (h : WebAssembly.Binary.Scalar.Immediate oc op bs) :
    Body.Scalar.Immediate (readerByte oc) (.plain op) (readerBytes bs) := by
  cases h with
  | unreachable => exact .unreachable
  | nop => exact .nop
  | return_ => exact .return_
  | drop => exact .drop
  | select => exact .select
  | memorySize => exact .memorySize
  | memoryGrow => exact .memoryGrow
  | br _ h =>
    obtain ⟨i, rfl, hi⟩ := readerIndex h
    exact .br i hi
  | brIf _ h =>
    obtain ⟨i, rfl, hi⟩ := readerIndex h
    exact .brIf i hi
  | call _ h =>
    obtain ⟨i, rfl, hi⟩ := readerIndex h
    exact .call i hi
  | callIndirect _ h =>
    obtain ⟨i, rfl, hi⟩ := readerIndex h
    simp only [readerBytes, List.map_append, List.map_cons, List.map_nil]
    exact .callIndirect i hi
  | localGet _ h =>
    obtain ⟨i, rfl, hi⟩ := readerIndex h
    exact .localGet i hi
  | localSet _ h =>
    obtain ⟨i, rfl, hi⟩ := readerIndex h
    exact .localSet i hi
  | localTee _ h =>
    obtain ⟨i, rfl, hi⟩ := readerIndex h
    exact .localTee i hi
  | globalGet _ h =>
    obtain ⟨i, rfl, hi⟩ := readerIndex h
    exact .globalGet i hi
  | globalSet _ h =>
    obtain ⟨i, rfl, hi⟩ := readerIndex h
    exact .globalSet i hi
  | i32Const _ h =>
    obtain ⟨i, rfl, hi⟩ := readerS32 h
    exact .i32Const i hi
  | i64Const _ h =>
    obtain ⟨i, rfl, hi⟩ := readerS64 h
    exact .i64Const i hi
  | f32Const _ h =>
    obtain ⟨i, rfl, hi⟩ := readerFloat32 h
    exact .f32Const i hi
  | f64Const _ h =>
    obtain ⟨i, rfl, hi⟩ := readerFloat64 h
    exact .f64Const i hi

  | brTable xs d hc he hf =>
    obtain ⟨ys, rfl, hy⟩ := indices he
    obtain ⟨i, rfl, hi⟩ := readerIndex hf
    simp only [readerBytes, List.map_append, List.map_map, Function.comp_def]
    exact .brTable ys i (by simpa using readerLeb hc) hy hi
  | memory oc op arg hm ha ho =>
    obtain ⟨a, o⟩ := arg
    change WebAssembly.Binary.Leb128.U32Encoding _ a at ha
    change WebAssembly.Binary.Leb128.U32Encoding _ o at ho
    obtain ⟨align, rfl, ea⟩ := readerIndex ha
    obtain ⟨offset, rfl, eo⟩ := readerIndex ho
    let arg : code.MemArg := { align, offset }
    obtain ⟨row, hr, eq⟩ := memory arg hm
    simp only [readerBytes, List.map_append]
    change Body.Scalar.Immediate _ (.plain (op.op (Body.MemoryMeaning.memArg arg))) _
    rw [← eq]
    exact .memory _ row arg hr ea eo
  | numericInstruction oc op h => exact .numericInstruction _ op h

private theorem bulk {oc op bs} (h : WebAssembly.Binary.BulkBinary.Immediate oc op bs) :
    ∃ sub : U32, sub.val = oc ∧ Body.BulkBinary.Immediate sub op (readerBytes bs) := by
  cases h with
  | memoryInit _ hi =>
    obtain ⟨i, rfl, ei⟩ := readerIndex hi
    refine ⟨8#u32, rfl, ?_⟩
    simp only [readerBytes, List.map_append, List.map_cons, List.map_nil]
    exact .memoryInit i ei
  | dataDrop _ hi =>
    obtain ⟨i, rfl, ei⟩ := readerIndex hi
    refine ⟨9#u32, rfl, ?_⟩
    simp only [readerBytes]
    exact .dataDrop i ei
  | memoryCopy =>
    refine ⟨10#u32, rfl, ?_⟩
    simp only [readerBytes, List.map_cons, List.map_nil]
    exact .memoryCopy
  | memoryFill =>
    refine ⟨11#u32, rfl, ?_⟩
    simp only [readerBytes, List.map_cons, List.map_nil]
    exact .memoryFill
  | tableInit _ _ he ht =>
    obtain ⟨e, rfl, ee⟩ := readerIndex he
    obtain ⟨t, rfl, et⟩ := readerIndex ht
    refine ⟨12#u32, rfl, ?_⟩
    simp only [readerBytes, List.map_append]
    exact .tableInit e t ee et
  | elemDrop _ hi =>
    obtain ⟨i, rfl, ei⟩ := readerIndex hi
    refine ⟨13#u32, rfl, ?_⟩
    simp only [readerBytes]
    exact .elemDrop i ei
  | tableCopy _ _ hd hs =>
    obtain ⟨d, rfl, ed⟩ := readerIndex hd
    obtain ⟨s, rfl, es⟩ := readerIndex hs
    refine ⟨14#u32, rfl, ?_⟩
    simp only [readerBytes, List.map_append]
    exact .tableCopy d s ed es
  | tableGrow _ hi =>
    obtain ⟨i, rfl, ei⟩ := readerIndex hi
    refine ⟨15#u32, rfl, ?_⟩
    simp only [readerBytes]
    exact .tableGrow i ei
  | tableSize _ hi =>
    obtain ⟨i, rfl, ei⟩ := readerIndex hi
    refine ⟨16#u32, rfl, ?_⟩
    simp only [readerBytes]
    exact .tableSize i ei
  | tableFill _ hi =>
    obtain ⟨i, rfl, ei⟩ := readerIndex hi
    refine ⟨17#u32, rfl, ?_⟩
    simp only [readerBytes]
    exact .tableFill i ei

private theorem reference {oc op bs} (h : WebAssembly.Binary.ReferencesBinary.Immediate oc op bs) :
    Body.ReferencesBinary.Immediate (readerByte oc) op (readerBytes bs) := by
  cases h with
  | refNull t =>
    rw [← referenceType_readerRef t]
    cases t <;> exact .refNull _
  | refIsNull => exact .refIsNull
  | selectTyped t h =>
    have eq := valueType_toSpec (readerType t)
    rw [valueType_readerType] at eq
    rw [eq]
    simp only [readerBytes, List.map_append, List.map_cons, List.map_nil, readerValueByte]
    exact .selectTyped _ (readerLeb h)
  | refFunc _ hi =>
    obtain ⟨i, rfl, ei⟩ := readerIndex hi
    simp only [readerBytes]
    exact .refFunc i ei
  | tableGet _ hi =>
    obtain ⟨i, rfl, ei⟩ := readerIndex hi
    simp only [readerBytes]
    exact .tableGet i ei
  | tableSet _ hi =>
    obtain ⟨i, rfl, ei⟩ := readerIndex hi
    simp only [readerBytes]
    exact .tableSet i ei
  | callIndirect _ _ hi ht =>
    obtain ⟨i, rfl, ei⟩ := readerIndex hi
    obtain ⟨t, rfl, et⟩ := readerIndex ht
    simp only [readerBytes, List.map_append]
    exact .callIndirect i t ei et

private theorem simd (sub : U32) {op bs} (h : WebAssembly.Binary.Simd.Immediate sub.val op bs) :
    Body.Simd.Immediate sub op (readerBytes bs) := by
  generalize he : sub.val = n at h
  cases h with
  | pure _ op h => exact .pure sub op (by simpa only [Body.Simd.operands, WebAssembly.Binary.Simd.nativeOperands, he, id_eq] using h)
  | lane _ op b h => exact .lane sub op (readerByte b) (by simpa only [Body.Simd.operands, WebAssembly.Binary.Simd.nativeOperands, he, id_eq] using h)
  | memory _ op arg hm hl ha ho =>
    obtain ⟨a, o⟩ := arg
    change WebAssembly.Binary.Leb128.U32Encoding _ a at ha
    change WebAssembly.Binary.Leb128.U32Encoding _ o at ho
    obtain ⟨align, rfl, ea⟩ := readerIndex ha
    obtain ⟨offset, rfl, eo⟩ := readerIndex ho
    simp only [readerBytes, List.map_append]
    exact WebAssembly.Binary.Simd.ImmediateWith.memory (rep := Body.Simd.operands) sub op {align, offset} (by simpa only [Body.Simd.operands, WebAssembly.Binary.Simd.nativeOperands, he, id_eq] using hm) hl ea eo
  | memoryLane _ op arg b hm hl ha ho =>
    obtain ⟨a, o⟩ := arg
    change WebAssembly.Binary.Leb128.U32Encoding _ a at ha
    change WebAssembly.Binary.Leb128.U32Encoding _ o at ho
    obtain ⟨align, rfl, ea⟩ := readerIndex ha
    obtain ⟨offset, rfl, eo⟩ := readerIndex ho
    simp only [readerBytes, List.map_append, List.map_cons, List.map_nil]
    exact WebAssembly.Binary.Simd.ImmediateWith.memoryLane (rep := Body.Simd.operands) sub op {align, offset} (readerByte b) (by simpa only [Body.Simd.operands, WebAssembly.Binary.Simd.nativeOperands, he, id_eq] using hm) hl ea eo
  | constant lo hi hl hh =>
    obtain ⟨lo, rfl, el⟩ := readerFloat64 hl
    obtain ⟨hi, rfl, eh⟩ := readerFloat64 hh
    have eq : sub = 12#u32 := UScalar.eq_of_val_eq he
    subst sub
    simp only [readerBytes, List.map_append]
    exact .constant lo hi el eh
  | shuffle lo hi hl hh =>
    obtain ⟨lo, rfl, el⟩ := readerFloat64 hl
    obtain ⟨hi, rfl, eh⟩ := readerFloat64 hh
    have eq : sub = 13#u32 := UScalar.eq_of_val_eq he
    subst sub
    simp only [readerBytes, List.map_append]
    exact .shuffle lo hi el eh

private theorem readBlock {bt bs} (h : WebAssembly.Binary.BlockEncoding bt bs) :
    ∃ v, Body.blockType v = bt ∧ Body.BlockEncoding v (readerBytes bs) := by
  suffices ∃ v, Body.blockType v = bt by
    obtain ⟨v, rfl⟩ := this
    exact ⟨v, rfl, by simpa only [Body.BlockEncoding, bytes_readerBytes] using h⟩
  cases h with
  | empty => exact ⟨.Empty, rfl⟩
  | result t =>
    exact ⟨.Value (readerType t), by simp [Body.blockType, ← valueType_toSpec (readerType t)]⟩
  | index n h =>
    have e := (SignedLeb33.encoding_iff (readerBytes _) n).mpr (by simpa only [bytes_readerBytes] using h)
    obtain ⟨_, _, _, _, _, _, _, _, hi⟩ := h
    have small : n < 2^32 := by change (n : Int) ≤ 4294967295 at hi; omega
    exact ⟨.TypeIndex (U32.ofNatCore n small), rfl⟩

theorem readToken {t bs} (h : WebAssembly.Binary.TokenEncoding t bs) :
    ∃ v, token v = t ∧ Body.TokenEncoding v (readerBytes bs) := by
  obtain ⟨oc, tail, rfl, hi⟩ := h
  suffices ∃ v, token v = t ∧ Body.Immediate (readerByte oc) v (readerBytes tail) by
    obtain ⟨v, rfl, hv⟩ := this
    exact ⟨v, rfl, _, _, rfl, hv⟩
  cases hi with
  | plain h => exact ⟨_, rfl, .plain (scalar h)⟩
  | signExtensionInstruction oc op h =>
    exact ⟨_, rfl, .signExtensionInstruction _ op h⟩
  | saturatingInstruction _ op h e =>
    obtain ⟨i, rfl, ei⟩ := readerIndex e
    exact ⟨_, rfl, .saturatingInstruction i op h ei⟩
  | reference h => exact ⟨_, rfl, .reference (reference h)⟩
  | bulk _ e h =>
    obtain ⟨i, rfl, hi⟩ := bulk h
    exact ⟨_, rfl, by simp only [readerBytes, List.map_append]; exact .bulk i (readerLeb e) hi⟩
  | simd _ e h =>
    obtain ⟨i, rfl, ei⟩ := readerIndex e
    exact ⟨_, rfl, by simp only [readerBytes, List.map_append]; exact .simd i ei (simd i h)⟩
  | block h => obtain ⟨v, rfl, e⟩ := readBlock h; exact ⟨.block v, rfl, .block e⟩
  | loop h => obtain ⟨v, rfl, e⟩ := readBlock h; exact ⟨.loop v, rfl, .loop e⟩
  | if_ h => obtain ⟨v, rfl, e⟩ := readBlock h; exact ⟨.if_ v, rfl, .if_ e⟩
  | else_ => exact ⟨.else_, rfl, .else_⟩
  | end_ => exact ⟨.end_, rfl, .end_⟩

end Itasca.Binary.Source
