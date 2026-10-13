import Itasca.Binary.Wasm1.Syntax
import Itasca.Binary.Wasm1.NumericMeaning
import Itasca.Binary.Wasm1.MemoryMeaning
import Itasca.Binary.Wasm1.BlockType
import Itasca.Binary.SignedLeb32
import Itasca.Binary.SignedLeb64
import Itasca.Binary.FloatBits
import Itasca.Spec.Instr
import Itasca.Spec.ScalarConst

/-!
# Wasm 1.0 instruction binary grammar

The handwritten binary grammar of Wasm 1.0 instructions. `Immediate` relates an opcode byte to a
token and its immediate bytes, `TokenEncoding` adds the opcode, and `At` places a token in a byte
slice. `Consumed` accumulates the tokens read so far and `BodyEncoding` is a complete body,
including its final `end`. The `At.of_*` lemmas assemble tokens from decoded immediates. The
grammar does not mention validation: opcode meaning comes from the tables in
`Binary/Wasm1/NumericMeaning` and `Binary/Wasm1/MemoryMeaning`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm1

/-- `bytes` is the slice of `data` from `start` to `next`, followed by the untouched suffix. -/
structure BytesAt (data : Slice U8) (start : Usize) (bytes : List U8) (next : Usize) : Prop where
  suffix : data.val.drop start.val = bytes ++ data.val.drop next.val
  length : next.val = start.val + bytes.length
  bound : next.val ≤ data.length

/-- The concatenated unsigned LEB128 entries of an index vector, without the leading count. -/
inductive IndicesEncoding : List U32 → List U8 → Prop where
  | nil : IndicesEncoding [] []
  | cons {idx indices first rest} : Leb128.Encoding first idx.val →
      IndicesEncoding indices rest → IndicesEncoding (idx :: indices) (first ++ rest)

/-- The immediate bytes that follow an opcode byte for a Wasm 1.0 token. Literal opcode values and
the numeric and memory opcode tables define the accepted syntax. -/
inductive Immediate : U8 → Token → List U8 → Prop where
  | unreachable : Immediate 0x00#u8 (.plain .UNREACHABLE) []
  | nop : Immediate 0x01#u8 (.plain .NOP) []
  | block (bt : code.BlockType) (hbt : Control.ScalarBlockType bt) : Immediate 0x02#u8 (.block bt) [Control.blockByte bt]
  | loop (bt : code.BlockType) (hbt : Control.ScalarBlockType bt) : Immediate 0x03#u8 (.loop bt) [Control.blockByte bt]
  | if_ (bt : code.BlockType) (hbt : Control.ScalarBlockType bt) : Immediate 0x04#u8 (.if_ bt) [Control.blockByte bt]
  | else_ : Immediate 0x05#u8 .else_ []
  | end_ : Immediate 0x0B#u8 .end_ []
  | br (idx : U32) {bytes} : Leb128.Encoding bytes idx.val →
      Immediate 0x0C#u8 (.plain (.BR (.mk_uN idx.val))) bytes
  | brIf (idx : U32) {bytes} : Leb128.Encoding bytes idx.val →
      Immediate 0x0D#u8 (.plain (.BR_IF (.mk_uN idx.val))) bytes
  | brTable (indices : List U32) (default : U32) {count entries final} :
      Leb128.Encoding count indices.length → IndicesEncoding indices entries →
      Leb128.Encoding final default.val →
      Immediate 0x0E#u8 (.plain (.BR_TABLE (indices.map (fun i => .mk_uN i.val)) (.mk_uN default.val)))
        (count ++ entries ++ final)
  | return_ : Immediate 0x0F#u8 (.plain .RETURN) []
  | call (idx : U32) {bytes} : Leb128.Encoding bytes idx.val →
      Immediate 0x10#u8 (.plain (.CALL (.mk_uN idx.val))) bytes
  | callIndirect (idx : U32) {bytes} : Leb128.Encoding bytes idx.val →
      Immediate 0x11#u8 (.plain (.CALL_INDIRECT (.mk_uN 0) (.mk_uN idx.val))) (bytes ++ [0#u8])
  | drop : Immediate 0x1A#u8 (.plain .DROP) []
  | select : Immediate 0x1B#u8 (.plain (.SELECT none)) []
  | localGet (idx : U32) {bytes} : Leb128.Encoding bytes idx.val →
      Immediate 0x20#u8 (.plain (.LOCAL_GET (.mk_uN idx.val))) bytes
  | localSet (idx : U32) {bytes} : Leb128.Encoding bytes idx.val →
      Immediate 0x21#u8 (.plain (.LOCAL_SET (.mk_uN idx.val))) bytes
  | localTee (idx : U32) {bytes} : Leb128.Encoding bytes idx.val →
      Immediate 0x22#u8 (.plain (.LOCAL_TEE (.mk_uN idx.val))) bytes
  | globalGet (idx : U32) {bytes} : Leb128.Encoding bytes idx.val →
      Immediate 0x23#u8 (.plain (.GLOBAL_GET (.mk_uN idx.val))) bytes
  | globalSet (idx : U32) {bytes} : Leb128.Encoding bytes idx.val →
      Immediate 0x24#u8 (.plain (.GLOBAL_SET (.mk_uN idx.val))) bytes
  | memory (opcode : U8) (operation : MemoryMeaning.Operation) (arg : code.MemArg)
      {alignment offset} (meaning : MemoryMeaning.opcodeMeaning opcode = some operation) :
      Leb128.Encoding alignment arg.align.val → Leb128.Encoding offset arg.offset.val →
      Immediate opcode (.plain (operation.op arg)) (alignment ++ offset)
  | memorySize : Immediate 0x3F#u8 (.plain .MEMORY_SIZE) [0#u8]
  | memoryGrow : Immediate 0x40#u8 (.plain .MEMORY_GROW) [0#u8]
  | i32Const (value : I32) {bytes} : SignedLeb32.Encoding bytes value.val →
      Immediate 0x41#u8 (.plain (Spec.i32Const value)) bytes
  | i64Const (value : I64) {bytes} : SignedLeb64.Encoding bytes value.val →
      Immediate 0x42#u8 (.plain (ScalarConst.i64 value)) bytes
  | f32Const (bits : U32) {bytes} : FloatBits.Encoding 4 bytes bits.val →
      Immediate 0x43#u8 (.plain (ScalarConst.f32 bits)) bytes
  | f64Const (bits : U64) {bytes} : FloatBits.Encoding 8 bytes bits.val →
      Immediate 0x44#u8 (.plain (ScalarConst.f64 bits)) bytes
  | numeric (opcode : U8) (operation : Numeric.Operation)
      (meaning : Numeric.opcodeMeaning opcode = some operation) :
      Immediate opcode (.plain operation.instruction) []

/-- A token as its opcode byte followed by its immediate bytes. -/
def TokenEncoding (token : Token) (bytes : List U8) : Prop :=
  ∃ opcode immediate, bytes = opcode :: immediate ∧ Immediate opcode token immediate

/-- A token is encoded by the interval from `start` to `next`. The suffix is unrestricted. -/
def At (data : Slice U8) (start : Usize) (token : Token) (next : Usize) : Prop :=
  ∃ bytes, TokenEncoding token bytes ∧ BytesAt data start bytes next

/-- The tokens read from `start` to the cursor, accumulated one `At` step at a time. -/
inductive Consumed (data : Slice U8) : Usize → List Token → Usize → Prop where
  | nil (pos : Usize) (bound : pos.val ≤ data.length) : Consumed data pos [] pos
  | snoc {start tokens pos token next} : Consumed data start tokens pos →
      At data pos token next → Consumed data start (tokens ++ [token]) next

/-- A complete function body: the tokens read from offset 0 reach the end of `data`, and end with
the final `end`. -/
def BodyEncoding (data : Slice U8) (ops : List instr) : Prop :=
  ∃ tokens next, Consumed data 0#usize tokens next ∧ next.val = data.length ∧ BodyTokens tokens ops

/-- The empty byte list occupies an empty interval at any cursor within the input. -/
theorem BytesAt.nil (data : Slice U8) (pos : Usize) (h : pos.val ≤ data.length) :
    BytesAt data pos [] pos := ⟨by simp, by simp, h⟩

/-- Adjacent byte intervals compose. -/
theorem BytesAt.append {data start middle next first rest}
    (hfirst : BytesAt data start first middle) (hrest : BytesAt data middle rest next) :
    BytesAt data start (first ++ rest) next := by
  refine ⟨?_, ?_, hrest.bound⟩
  · rw [hfirst.suffix, hrest.suffix, List.append_assoc]
  · simp only [List.length_append]
    have := hfirst.length
    have := hrest.length
    omega

/-- A single byte within the input occupies a one-byte interval. -/
theorem BytesAt.byte (data : Slice U8) (start next : Usize) (b : U8)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = b)
    (hnext : next.val = start.val + 1) : BytesAt data start [b] next := by
  refine ⟨?_, by simpa using hnext, by omega⟩
  rw [List.drop_eq_getElem_cons hstart, hbyte, hnext]
  rfl

/-- A token interval is nonempty and within the input. -/
theorem At.span {data start token next} (h : At data start token next) :
    start.val < next.val ∧ next.val ≤ data.length := by
  obtain ⟨_, ⟨op, imm, rfl, _⟩, hs⟩ := h
  have := hs.length
  simp only [List.length_cons] at this
  exact ⟨by omega, hs.bound⟩

/-- Composes an opcode byte with an immediate byte span. -/
theorem At.of_immediate {data start pos next opcode token immediate}
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = opcode)
    (hpos : pos.val = start.val + 1)
    (himmediate : Immediate opcode token immediate) (hspan : BytesAt data pos immediate next) :
    At data start token next := by
  exact ⟨opcode :: immediate, ⟨opcode, immediate, rfl, himmediate⟩,
    by simpa using (BytesAt.byte data start pos opcode hstart hbyte hpos).append hspan⟩

/-- A token with no immediate bytes ends right after its opcode. -/
theorem At.no_immediate {data start next opcode token}
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = opcode)
    (hnext : next.val = start.val + 1) (himm : Immediate opcode token []) :
    At data start token next := by
  exact .of_immediate hstart hbyte hnext himm (.nil data next (by omega))

/-- A consumed span is within the input. -/
theorem Consumed.span {data start tokens next} (h : Consumed data start tokens next) :
    start.val ≤ next.val ∧ next.val ≤ data.length := by
  induction h with
  | nil hb => exact ⟨Nat.le_refl _, hb⟩
  | snoc _ ha ih => have := ha.span; omega

/-- Consumed spans compose. -/
theorem Consumed.append {data start middle next first rest}
    (hfirst : Consumed data start first middle) (hrest : Consumed data middle rest next) :
    Consumed data start (first ++ rest) next := by
  induction hrest with
  | nil _ => simpa using hfirst
  | snoc _ ha ih => simpa [List.append_assoc] using Consumed.snoc ih ha

end Itasca.Wasm1

namespace Itasca.Wasm1

/-- Index vector entries compose. -/
theorem IndicesEncoding.append {first rest bs cs}
    (hfirst : IndicesEncoding first bs) (hrest : IndicesEncoding rest cs) :
    IndicesEncoding (first ++ rest) (bs ++ cs) := by
  induction hfirst with
  | nil => simpa using hrest
  | cons hb _ ih => simpa [List.append_assoc] using IndicesEncoding.cons hb ih

/-- Appending one entry to an index vector. -/
theorem IndicesEncoding.snoc {indices bytes idx last}
    (h : IndicesEncoding indices bytes) (hlast : Leb128.Encoding last idx.val) :
    IndicesEncoding (indices ++ [idx]) (bytes ++ last) := by
  simpa using h.append (.cons hlast .nil)

/-- A token whose immediate is a single unsigned LEB128 value, from a decoded `u32`. -/
theorem At.of_u32 {data start pos next opcode token} (value : U32)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = opcode)
    (hpos : pos.val = start.val + 1)
    (himm : ∀ bytes, Leb128.Encoding bytes value.val → Immediate opcode token bytes)
    (hdecoded : Leb128.Decoded data pos value next) : At data start token next := by
  obtain ⟨bytes, hs, hl, hb, he⟩ := hdecoded
  exact .of_immediate hstart hbyte hpos (himm bytes he) ⟨hs, hl, hb⟩

/-- An `i32.const` token from a decoded signed 32-bit LEB128. -/
theorem At.of_s32 {data start pos next} (value : I32)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = 0x41#u8)
    (hpos : pos.val = start.val + 1)
    (hdecoded : SignedLeb32.Decoded data pos value.val next) :
    At data start (.plain (Spec.i32Const value)) next := by
  obtain ⟨bytes, hs, hl, hb, he⟩ := hdecoded
  exact .of_immediate hstart hbyte hpos (.i32Const value he) ⟨hs, hl, hb⟩

/-- An `i64.const` token from a decoded signed 64-bit LEB128. -/
theorem At.of_s64 {data start pos next} (value : I64)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = 0x42#u8)
    (hpos : pos.val = start.val + 1)
    (hdecoded : SignedLeb64.Decoded data pos value.val next) :
    At data start (.plain (ScalarConst.i64 value)) next := by
  obtain ⟨bytes, hs, hl, hb, he⟩ := hdecoded
  exact .of_immediate hstart hbyte hpos (.i64Const value he) ⟨hs, hl, hb⟩

/-- An `f32.const` token from four decoded bytes. -/
theorem At.of_f32 {data start pos next} (bits : U32)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = 0x43#u8)
    (hpos : pos.val = start.val + 1)
    (hdecoded : FloatBits.Decoded 4 data pos bits.val next) :
    At data start (.plain (ScalarConst.f32 bits)) next := by
  obtain ⟨bytes, hs, hl, hb, he⟩ := hdecoded
  exact .of_immediate hstart hbyte hpos (.f32Const bits he) ⟨hs, by rw [he.1]; exact hl, hb⟩

/-- An `f64.const` token from eight decoded bytes. -/
theorem At.of_f64 {data start pos next} (bits : U64)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = 0x44#u8)
    (hpos : pos.val = start.val + 1)
    (hdecoded : FloatBits.Decoded 8 data pos bits.val next) :
    At data start (.plain (ScalarConst.f64 bits)) next := by
  obtain ⟨bytes, hs, hl, hb, he⟩ := hdecoded
  exact .of_immediate hstart hbyte hpos (.f64Const bits he) ⟨hs, by rw [he.1]; exact hl, hb⟩

/-- A token whose immediate is a single byte, such as a block type or a reserved zero. -/
theorem At.of_byte {data : Slice U8} {start pos next : Usize} {opcode token} (immediate : U8)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = opcode)
    (hpos : pos.val = start.val + 1) (himm : Immediate opcode token [immediate])
    (hbound : pos.val < data.length) (hvalue : data.val[pos.val] = immediate)
    (hnext : next.val = pos.val + 1) : At data start token next := by
  exact .of_immediate hstart hbyte hpos himm (.byte data pos next immediate hbound hvalue hnext)

/-- A `call_indirect` token from a decoded type index and the reserved zero byte. -/
theorem At.of_index_zero {data start pos middle next} (idx : U32)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = 0x11#u8)
    (hpos : pos.val = start.val + 1) (hindex : Leb128.Decoded data pos idx middle)
    (hbound : middle.val < data.length) (hzero : data.val[middle.val] = 0#u8)
    (hnext : next.val = middle.val + 1) :
    At data start (.plain (.CALL_INDIRECT (.mk_uN 0) (.mk_uN idx.val))) next := by
  obtain ⟨bytes, hs, hl, hb, he⟩ := hindex
  exact .of_immediate hstart hbyte hpos (.callIndirect idx he)
    ((show BytesAt data pos bytes middle from ⟨hs, hl, hb⟩).append
      (.byte data middle next 0#u8 hbound hzero hnext))

/-- A memory access token from a decoded alignment and offset. -/
theorem At.of_memory {data start pos middle next opcode} (operation : MemoryMeaning.Operation)
    (arg : code.MemArg) (meaning : MemoryMeaning.opcodeMeaning opcode = some operation)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = opcode)
    (hpos : pos.val = start.val + 1) (halign : Leb128.Decoded data pos arg.align middle)
    (hoffset : Leb128.Decoded data middle arg.offset next) :
    At data start (.plain (operation.op arg)) next := by
  obtain ⟨alignBytes, has, hal, hab, hae⟩ := halign
  obtain ⟨os, hos, hol, hob, hoe⟩ := hoffset
  exact .of_immediate hstart hbyte hpos (.memory opcode operation arg meaning hae hoe)
    ((show BytesAt data pos alignBytes middle from ⟨has, hal, hab⟩).append ⟨hos, hol, hob⟩)

end Itasca.Wasm1

namespace Itasca.Wasm1

/-- A structured instruction header token from a decoded one-byte block type. -/
theorem At.of_block_type {data start pos next opcode token} (bt : code.BlockType)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = opcode)
    (hpos : pos.val = start.val + 1)
    (himm : Control.ScalarBlockType bt → Immediate opcode token [Control.blockByte bt])
    (hdecoded : Control.BlockDecoded data pos bt next) : At data start token next := by
  obtain ⟨hb, hv, hn, _, hbt⟩ := hdecoded
  exact .of_byte (Control.blockByte bt) hstart hbyte hpos (himm hbt) hb hv hn

end Itasca.Wasm1
