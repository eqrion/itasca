import Itasca.Binary.Source
import Itasca.Binary.LebBytes

namespace Itasca.Binary.Source
open Aeneas.Std WebAssembly

private theorem floatPayload (bs : List U8) :
    WebAssembly.Binary.FloatBits.payload (bytes bs) = Itasca.Binary.FloatBits.payload bs := by
  induction bs with
  | nil => rfl
  | cons x xs ih =>
    change x.val + 256 * WebAssembly.Binary.FloatBits.payload (bytes xs) = _
    rw [ih]
    rfl

theorem floatBits {n bs v} : Itasca.Binary.FloatBits.Encoding n bs v ↔
    WebAssembly.Binary.FloatBits.Encoding n (bytes bs) v := by
  change (_ ∧ v = Itasca.Binary.FloatBits.payload bs) ↔
    (_ ∧ v = WebAssembly.Binary.FloatBits.payload (bytes bs))
  rw [floatPayload, List.length_map]

private theorem indices {xs bs} (h : Body.Scalar.IndicesEncoding xs bs) :
    WebAssembly.Binary.Scalar.IndicesEncoding (xs.map UScalar.val) (bytes bs) := by
  induction h with
  | nil => exact .nil
  | cons h _ ih =>
    simp only [bytes, List.map_append, List.map_cons]
    exact .cons ((Leb128.encoding_iff _ _).mp h) ih

private theorem memory {opcode operation} (arg : code.MemArg)
    (h : Body.MemoryMeaning.opcodeMeaning opcode = some operation) :
    ∃ native, WebAssembly.Binary.MemoryMeaning.opcodeMeaning (sourceByte opcode) = some native ∧
      native.op (Body.MemoryMeaning.memArg arg) = operation.op arg := by
  unfold Body.MemoryMeaning.opcodeMeaning at h
  unfold WebAssembly.Binary.MemoryMeaning.opcodeMeaning WebAssembly.Binary.MemoryMeaning.opcodeTable
  rw [show (sourceByte opcode).toNat = opcode.val from rfl]
  split at h <;> try contradiction
  all_goals cases h; exact ⟨_, rfl, rfl⟩

private theorem scalar {oc op bs} (h : Body.Scalar.Immediate oc (.plain op) bs) :
    WebAssembly.Binary.Scalar.Immediate (sourceByte oc) op (bytes bs) := by
  cases h with
  | unreachable => exact .unreachable
  | nop => exact .nop
  | return_ => exact .return_
  | drop => exact .drop
  | select => exact .select
  | memorySize => exact .memorySize
  | memoryGrow => exact .memoryGrow
  | br i h => exact .br i.val ((Leb128.encoding_iff _ _).mp h)
  | brIf i h => exact .brIf i.val ((Leb128.encoding_iff _ _).mp h)
  | call i h => exact .call i.val ((Leb128.encoding_iff _ _).mp h)
  | callIndirect i h =>
    simp only [bytes, List.map_append, List.map_cons, List.map_nil]
    exact .callIndirect i.val ((Leb128.encoding_iff _ _).mp h)
  | localGet i h => exact .localGet i.val ((Leb128.encoding_iff _ _).mp h)
  | localSet i h => exact .localSet i.val ((Leb128.encoding_iff _ _).mp h)
  | localTee i h => exact .localTee i.val ((Leb128.encoding_iff _ _).mp h)
  | globalGet i h => exact .globalGet i.val ((Leb128.encoding_iff _ _).mp h)
  | globalSet i h => exact .globalSet i.val ((Leb128.encoding_iff _ _).mp h)

  | brTable xs i hc he hf =>
    simp only [bytes, List.map_append]
    have e := WebAssembly.Binary.Scalar.ImmediateWith.brTable (r := WebAssembly.Binary.Scalar.nativeOperands) (xs.map UScalar.val) i.val
        (by simpa using (Leb128.encoding_iff _ _).mp hc) (indices he) ((Leb128.encoding_iff _ _).mp hf)
    simp only [List.map_map, Function.comp_def] at e
    exact e
  | memory oc operation arg hm ha ho =>
    obtain ⟨native, hn, eq⟩ := memory arg hm
    change WebAssembly.Binary.Scalar.Immediate _ (operation.op arg) _
    rw [← eq]
    simp only [bytes, List.map_append]
    exact WebAssembly.Binary.Scalar.ImmediateWith.memory (r := WebAssembly.Binary.Scalar.nativeOperands)
      (sourceByte oc) native (arg.align.val, arg.offset.val) hn ((Leb128.encoding_iff _ _).mp ha)
      ((Leb128.encoding_iff _ _).mp ho)
  | i32Const v h => exact .i32Const v.val ((SignedLeb32.encoding_iff _ _).mp h)
  | i64Const v h => exact .i64Const v.val ((SignedLeb64.encoding_iff _ _).mp h)
  | f32Const v h => exact .f32Const v.val (floatBits.mp h)
  | f64Const v h => exact .f64Const v.val (floatBits.mp h)
  | numericInstruction oc op h => exact .numericInstruction _ op h

theorem bulkImmediate {oc op bs} (h : Body.BulkBinary.Immediate oc op bs) :
    WebAssembly.Binary.BulkBinary.Immediate oc.val op (bytes bs) := by
  cases h <;> simp only [bytes, List.map_append, List.map_cons, List.map_nil]
  case memoryInit i _ h => exact .memoryInit i.val ((Leb128.encoding_iff _ _).mp h)
  case dataDrop i h => exact .dataDrop i.val ((Leb128.encoding_iff _ _).mp h)
  case memoryCopy   => exact .memoryCopy
  case memoryFill   => exact .memoryFill
  case tableInit e t _ _ he ht => exact .tableInit e.val t.val ((Leb128.encoding_iff _ _).mp he) ((Leb128.encoding_iff _ _).mp ht)
  case elemDrop i h => exact .elemDrop i.val ((Leb128.encoding_iff _ _).mp h)
  case tableCopy d s _ _ hd hs => exact .tableCopy d.val s.val ((Leb128.encoding_iff _ _).mp hd) ((Leb128.encoding_iff _ _).mp hs)
  case tableGrow i h => exact .tableGrow i.val ((Leb128.encoding_iff _ _).mp h)
  case tableSize i h => exact .tableSize i.val ((Leb128.encoding_iff _ _).mp h)
  case tableFill i h => exact .tableFill i.val ((Leb128.encoding_iff _ _).mp h)

theorem referenceImmediate {oc op bs} (h : Body.ReferencesBinary.Immediate oc op bs) :
    WebAssembly.Binary.ReferencesBinary.Immediate (sourceByte oc) op (bytes bs) := by
  cases h <;> simp only [bytes, List.map_append, List.map_cons, List.map_nil, referenceByte_eq,
    valueByte_eq]
  case refNull t => exact .refNull _
  case refIsNull => exact .refIsNull
  case refFunc i h => exact .refFunc _ ((Leb128.encoding_iff _ _).mp h)
  case selectTyped t _ h =>
    rw [← valueType_toSpec t]
    exact .selectTyped (valueType t) ((Leb128.encoding_iff _ _).mp h)
  case tableGet i h => exact .tableGet _ ((Leb128.encoding_iff _ _).mp h)
  case tableSet i h => exact .tableSet _ ((Leb128.encoding_iff _ _).mp h)
  case callIndirect i t hi ht =>
    exact .callIndirect _ _ ((Leb128.encoding_iff _ _).mp hi) ((Leb128.encoding_iff _ _).mp ht)

theorem simdImmediate {oc op bs} (h : Body.Simd.Immediate oc op bs) :
    WebAssembly.Binary.Simd.Immediate oc.val op (bytes bs) := by
  cases h <;> simp only [bytes, List.map_append, List.map_cons, List.map_nil]
  case pure h => exact .pure _ _ h
  case lane op lane h => exact .lane _ op (sourceByte lane) h
  case memory op arg _ _ hl ha ho hm =>
    exact .memory _ op (arg.align.val, arg.offset.val) hm hl ((Leb128.encoding_iff _ _).mp ha)
      ((Leb128.encoding_iff _ _).mp ho)
  case memoryLane op arg lane _ _ hl ha ho hm =>
    exact .memoryLane _ op (arg.align.val, arg.offset.val) (sourceByte lane) hm hl
      ((Leb128.encoding_iff _ _).mp ha) ((Leb128.encoding_iff _ _).mp ho)
  case constant lo hi hl hh => exact .constant _ _ (floatBits.mp hl) (floatBits.mp hh)
  case shuffle lo hi _ _ hl hh =>
    exact .shuffle lo.val hi.val (floatBits.mp hl) (floatBits.mp hh)

theorem tokenImmediate {oc t bs} (h : Body.Immediate oc t bs) :
    WebAssembly.Binary.Immediate (sourceByte oc) (token t) (bytes bs) := by
  cases h <;> simp only [bytes, List.map_append]
  case plain h => exact .plain (scalar h)
  case signExtensionInstruction h => exact .signExtensionInstruction _ _ h
  case saturatingInstruction oc op h e =>
    exact .saturatingInstruction oc.val op h ((Leb128.encoding_iff _ _).mp e)
  case reference h => exact .reference (referenceImmediate h)
  case bulk e h => exact .bulk _ ((Leb128.encoding_iff _ _).mp e) (bulkImmediate h)
  case simd e h => exact .simd _ ((Leb128.encoding_iff _ _).mp e) (simdImmediate h)
  case block h => exact .block h
  case loop h => exact .loop h
  case if_ h => exact .if_ h
  case else_ => exact .else_
  case end_ => exact .end_

theorem tokenEncoding {t bs} (h : Body.TokenEncoding t bs) :
    WebAssembly.Binary.TokenEncoding (token t) (bytes bs) := by
  obtain ⟨oc, tail, rfl, hi⟩ := h
  exact ⟨_, _, rfl, tokenImmediate hi⟩

theorem emits {ts ops} (h : Body.Emits ts ops) :
    WebAssembly.Binary.Emits (ts.map token) ops := by
  induction h with
  | nil => exact .nil
  | simple _ hs ih => cases hs with
    | plain op wf => simpa [token] using WebAssembly.Binary.EmitsWith.simple (toSpec := id) ih (.plain _ wf)
  | block bt _ _ ih ib => simpa [token] using WebAssembly.Binary.EmitsWith.block (toSpec := id) (Body.blockType bt) ih ib
  | loop bt _ _ ih ib => simpa [token] using WebAssembly.Binary.EmitsWith.loop (toSpec := id) (Body.blockType bt) ih ib
  | ifElse bt _ _ _ ih it ie => simpa [token] using
      WebAssembly.Binary.EmitsWith.ifElse (toSpec := id) (Body.blockType bt) ih it ie
  | ifEnd bt _ _ ih it => simpa [token] using WebAssembly.Binary.EmitsWith.ifEnd (toSpec := id) (Body.blockType bt) ih it

theorem bodyTokens {ts ops} (h : Body.BodyTokens ts ops) :
    WebAssembly.Binary.BodyTokens (ts.map token) ops := by
  obtain ⟨inner, rfl, h⟩ := h
  exact ⟨inner.map token, by simp [token], emits h⟩

end Itasca.Binary.Source

namespace Itasca.Body
open Aeneas.Std

theorem BlockEncoding.reader_form {bt bs} : BlockEncoding bt bs ↔
    match bt with
    | .Empty => bs = [64#u8]
    | .Value t => bs = [Binary.valueByte t]
    | .TypeIndex i => Binary.SignedLeb33.Encoding bs i.val := by
  cases bt with
  | Empty =>
    rw [BlockEncoding, blockType, WebAssembly.Binary.BlockEncoding.empty_iff]
    exact ⟨fun h => (Binary.Source.readerBytes_bytes bs).symm.trans (congrArg Binary.Source.readerBytes h),
      fun h => h ▸ rfl⟩
  | Value t =>
    rw [BlockEncoding, blockType, ← Binary.Source.valueType_toSpec t, WebAssembly.Binary.BlockEncoding.result_iff]
    exact ⟨fun h => (Binary.Source.readerBytes_bytes bs).symm.trans (congrArg Binary.Source.readerBytes h),
      fun h => h ▸ rfl⟩
  | TypeIndex i =>
    rw [BlockEncoding, blockType, WebAssembly.Binary.BlockEncoding.index_iff]
    exact (Binary.SignedLeb33.encoding_iff _ _).symm

end Itasca.Body
