import Itasca.Binary.Definitions
import Itasca.Results.Definitions.Binary
import Itasca.Binary.Body.Syntax
import Itasca.Binary.Scalar.NumericOperations
import Itasca.Support.Translation
import Mathlib.Tactic.IntervalCases
import Itasca.Binary.LebReaders
import Itasca.Spec.Typing

open WebAssembly

/-!
Proofs for Binary / Scalar.

This module collects BlockType, Encoding.
Each section documents its contracts and consumers.
-/

/-! ## BlockType -/

section

/-!
# Scalar block-type encodings

`ScalarBlockByte bt b` relates the empty block type and four numeric result types
to their one-byte spelling. This is an internal case of the complete block-type
grammar, shared by scalar instruction proofs.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.Scalar

/-- A byte spells at most one block type, and a block type has at most one spelling. -/
theorem ScalarBlockByte.unique {bt bt' b b'} (h : ScalarBlockByte bt b) (h' : ScalarBlockByte bt' b')
    (he : b = b' ∨ bt = bt') : bt = bt' ∧ b = b' := by
  cases h <;> cases h' <;> simp_all [Binary.Source.readerValueType] <;> exact (by decide : ¬ _) he

end Itasca.Body.Scalar

end

/-! ## Encoding -/

section

/-!
# Encoding

Scalar opcode meanings and immediate spellings establish the reusable scalar token grammar. Branch-table label encodings and grammar completeness support complete body decoding.
-/

/-! ## NumericMeaning -/

section

/-!
# scalar numeric opcodes

`Body.Numeric.opcodeMeaning` is a literal table of the scalar numeric opcodes `0x45` to `0xbf`. Each
row is an `Body.Numeric.Operation`: a SpecTec instruction with its operand and result types and a
proof that it is well formed and that `Instr_ok` types it with that stack effect. The table is
written independently of the extracted opcode dispatch.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.Numeric

/-- Translating `valueType t` gives the SpecTec value type of `t`. -/
@[simp] theorem num_type_value (t : numtype) :
    Translation.valueType (valueType t) = valtype_numtype t := by cases t <;> rfl

/-- The operand types of an operation. -/
def Operation.inputs (op : Operation) : List wasm_types.ValueType :=
  if op.binary then [op.input, op.input] else [op.input]

/-- `op` is the numeric operation of the opcode. -/
def NumericOp (opcode : U8) (op : Operation) : Prop := opcodeMeaning opcode = some op

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- Exactly the opcodes `0x45` to `0xbf` have a numeric meaning. -/
theorem opcode_meaning_is_some (opcode : U8) :
    (opcodeMeaning opcode).isSome = decide (0x45 ≤ opcode.val ∧ opcode.val ≤ 0xBF) := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  change n < 256 at hn
  interval_cases n <;> rfl

/-- Numeric opcodes lie between `0x45` and `0xbf`. -/
theorem NumericOp.bounds {opcode : U8} {op : Operation} (h : NumericOp opcode op) :
    0x45 ≤ opcode.val ∧ opcode.val ≤ 0xBF := by
  have hs := opcode_meaning_is_some opcode
  rw [h] at hs
  simpa using hs.symm

end Itasca.Body.Numeric

end

/-! ## Encoding -/

section

/-!
# scalar instruction binary grammar

The handwritten binary grammar of scalar instructions. `Immediate` relates an opcode byte to a
token and its immediate bytes, `TokenEncoding` adds the opcode, and `At` places a token in a byte
slice. `Consumed` accumulates the tokens read so far and `BodyEncoding` is a complete body,
including its final `end`. The `At.of_*` lemmas assemble tokens from decoded immediates. The
grammar does not mention validation: opcode meaning comes from the tables in
`Results/Definitions/Binary/ScalarInstructions`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.Scalar

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

/-- Consumed spans compose. -/
theorem Consumed.append {data start middle next first rest}
    (hfirst : Consumed data start first middle) (hrest : Consumed data middle rest next) :
    Consumed data start (first ++ rest) next := by
  induction hrest with
  | nil _ => simpa using hfirst
  | snoc _ ha ih => simpa [List.append_assoc] using Consumed.snoc ih ha

end Itasca.Body.Scalar

namespace Itasca.Body.Scalar

/-- Index vector entries compose. -/
theorem IndicesEncoding.append {first rest bs cs}
    (hfirst : IndicesEncoding first bs) (hrest : IndicesEncoding rest cs) :
    IndicesEncoding (first ++ rest) (bs ++ cs) := by
  induction hfirst with
  | nil => simpa using hrest
  | cons hb _ ih => simpa [List.append_assoc] using WebAssembly.Binary.Scalar.IndicesEncodingWith.cons hb ih

/-- Appending one entry to an index vector. -/
theorem IndicesEncoding.snoc {indices bytes idx last}
    (h : IndicesEncoding indices bytes) (hlast : Binary.Leb128.Encoding last idx.val) :
    IndicesEncoding (indices ++ [idx]) (bytes ++ last) := by
  simpa using h.append (.cons hlast .nil)

/-- A token whose immediate is a single unsigned LEB128 value, from a decoded `u32`. -/
theorem At.of_u32 {data start pos next opcode token} (value : U32)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = opcode)
    (hpos : pos.val = start.val + 1)
    (himm : ∀ bytes, Binary.Leb128.Encoding bytes value.val → Immediate opcode token bytes)
    (hdecoded : Binary.Leb128.Decoded data pos value next) : At data start token next := by
  obtain ⟨bytes, hs, hl, hb, he⟩ := hdecoded
  exact .of_immediate hstart hbyte hpos (himm bytes he) ⟨hs, hl, hb⟩

/-- An `i32.const` token from a decoded signed 32-bit LEB128. -/
theorem At.of_s32 {data start pos next} (value : I32)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = 0x41#u8)
    (hpos : pos.val = start.val + 1)
    (hdecoded : Binary.SignedLeb32.Decoded data pos value.val next) :
    At data start (.plain (Spec.i32Const value)) next := by
  obtain ⟨bytes, hs, hl, hb, he⟩ := hdecoded
  exact .of_immediate hstart hbyte hpos (.i32Const value he) ⟨hs, hl, hb⟩

/-- An `i64.const` token from a decoded signed 64-bit LEB128. -/
theorem At.of_s64 {data start pos next} (value : I64)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = 0x42#u8)
    (hpos : pos.val = start.val + 1)
    (hdecoded : Binary.SignedLeb64.Decoded data pos value.val next) :
    At data start (.plain (Spec.Constants.i64 value)) next := by
  obtain ⟨bytes, hs, hl, hb, he⟩ := hdecoded
  exact .of_immediate hstart hbyte hpos (.i64Const value he) ⟨hs, hl, hb⟩

/-- An `f32.const` token from four decoded bytes. -/
theorem At.of_f32 {data start pos next} (bits : U32)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = 0x43#u8)
    (hpos : pos.val = start.val + 1)
    (hdecoded : Binary.FloatBits.Decoded 4 data pos bits.val next) :
    At data start (.plain (Spec.Constants.f32 bits)) next := by
  obtain ⟨bytes, hs, hl, hb, he⟩ := hdecoded
  exact .of_immediate hstart hbyte hpos (.f32Const bits he) ⟨hs, by rw [he.1]; exact hl, hb⟩

/-- An `f64.const` token from eight decoded bytes. -/
theorem At.of_f64 {data start pos next} (bits : U64)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = 0x44#u8)
    (hpos : pos.val = start.val + 1)
    (hdecoded : Binary.FloatBits.Decoded 8 data pos bits.val next) :
    At data start (.plain (Spec.Constants.f64 bits)) next := by
  obtain ⟨bytes, hs, hl, hb, he⟩ := hdecoded
  exact .of_immediate hstart hbyte hpos (.f64Const bits he) ⟨hs, by rw [he.1]; exact hl, hb⟩

/-- A token whose immediate is a single byte, such as a block type or a reserved zero. -/
theorem At.of_byte {data : Slice U8} {start pos next : Usize} {opcode token} (immediate : U8)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = opcode)
    (hpos : pos.val = start.val + 1) (himm : Immediate opcode token [immediate])
    (hbound : pos.val < data.length) (hvalue : data.val[pos.val] = immediate)
    (hnext : next.val = pos.val + 1) : At data start token next := by
  exact .of_immediate hstart hbyte hpos himm (.byte data pos next immediate hbound hvalue hnext)

/-- A memory access token from a decoded alignment and offset. -/
theorem At.of_memory {data start pos middle next opcode} (operation : Body.MemoryMeaning.Operation)
    (arg : code.MemArg) (meaning : Body.MemoryMeaning.opcodeMeaning opcode = some operation)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = opcode)
    (hpos : pos.val = start.val + 1) (halign : Binary.Leb128.Decoded data pos arg.align middle)
    (hoffset : Binary.Leb128.Decoded data middle arg.offset next) :
    At data start (.plain (operation.op arg)) next := by
  obtain ⟨alignBytes, has, hal, hab, hae⟩ := halign
  obtain ⟨os, hos, hol, hob, hoe⟩ := hoffset
  exact .of_immediate hstart hbyte hpos (.memory opcode operation arg meaning hae hoe)
    ((show BytesAt data pos alignBytes middle from ⟨has, hal, hab⟩).append ⟨hos, hol, hob⟩)

end Itasca.Body.Scalar

end

/-! ## BrTableLabels -/

section

/-!
# Branch table immediates

Byte-level description of the `br_table` immediate: a count, that many labels and a default
label, each an unsigned LEB128. `Body.BrTable.Decoded` describes it at a cursor, and
`Body.Scalar.At.of_br_table` and `Body.Scalar.At.of_table_decoded` assemble a `br_table` token from it.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.BrTable

/-- A run of consecutive unsigned LEB128 labels decoded from the cursor. -/
inductive LabelsDecoded (data : Slice U8) (start : Usize) : List U32 → Usize → Prop where
  | nil : LabelsDecoded data start [] start
  | snoc {depths pos next depth} : LabelsDecoded data start depths pos →
      Binary.Leb128.Decoded data pos depth next → LabelsDecoded data start (depths ++ [depth]) next

/-- A label run stays within the input. -/
theorem LabelsDecoded.span {data start depths next}
    (h : LabelsDecoded data start depths next) (hb : start.val ≤ data.length) :
    start.val ≤ next.val ∧ next.val ≤ data.length := by
  induction h with
  | nil => exact ⟨le_rfl, hb⟩
  | snoc h hd ih =>
    have hs := hd.span
    omega

/-- The `br_table` immediate: a count, exactly that many labels and a default label. -/
def Decoded (data : Slice U8) (start : Usize) (depths : List U32)
    (default : U32) (next : Usize) : Prop :=
  ∃ count first last, Binary.Leb128.Decoded data start count first ∧
    depths.length = count.val ∧ LabelsDecoded data first depths last ∧
    Binary.Leb128.Decoded data last default next

/-- A label run has an `IndicesEncoding` over the bytes it occupies. -/
theorem LabelsDecoded.bytes {data start depths next}
    (h : LabelsDecoded data start depths next) (hb : start.val ≤ data.length) :
    ∃ bytes, Body.Scalar.IndicesEncoding depths bytes ∧ Body.Scalar.BytesAt data start bytes next := by
  induction h with
  | nil => exact ⟨[], .nil, .nil data start hb⟩
  | snoc _ hd ih =>
    obtain ⟨before, he, hs⟩ := ih
    obtain ⟨last, hlast, hlen, hbound, hencoding⟩ := hd
    exact ⟨before ++ last, he.snoc hencoding, hs.append ⟨hlast, hlen, hbound⟩⟩

end Itasca.Body.BrTable

namespace Itasca.Body.Scalar

/-- A decoded count, label run and default label give a `br_table` token. -/
theorem At.of_br_table {data start pos first last next} (count : U32)
    (depths : List U32) (default : U32)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = 0x0E#u8)
    (hpos : pos.val = start.val + 1) (hcount : Binary.Leb128.Decoded data pos count first)
    (hlen : depths.length = count.val) (hdepths : Body.BrTable.LabelsDecoded data first depths last)
    (hdefault : Binary.Leb128.Decoded data last default next) :
    At data start (.plain (.BR_TABLE (depths.map (fun d => .mk_uN d.val)) (.mk_uN default.val))) next := by
  obtain ⟨countBytes, hc, hcl, hcb, hce⟩ := hcount
  obtain ⟨depthBytes, hde, hds⟩ := hdepths.bytes hcb
  obtain ⟨defaultBytes, hd, hdl, hdb, hde'⟩ := hdefault
  exact .of_immediate hstart hbyte hpos (.brTable depths default (by simpa [hlen] using hce) hde hde')
    (((show BytesAt data pos countBytes first from ⟨hc, hcl, hcb⟩).append hds).append ⟨hd, hdl, hdb⟩)

/-- A decoded `br_table` immediate gives a `br_table` token. -/
theorem At.of_table_decoded {data start pos next} (depths : List U32) (default : U32)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = 0x0E#u8)
    (hpos : pos.val = start.val + 1) (hdecoded : Body.BrTable.Decoded data pos depths default next) :
    At data start (.plain (.BR_TABLE (depths.map (fun d => .mk_uN d.val)) (.mk_uN default.val))) next := by
  obtain ⟨count, first, last, hc, hl, hd, hf⟩ := hdecoded
  exact .of_br_table count depths default hstart hbyte hpos hc hl hd hf

end Itasca.Body.Scalar

end

/-! ## EncodingComplete -/

section

/-!
# Reading scalar encodings

Splitting lemmas for `BytesAt`, `Consumed` and `Body.BrTable.LabelsDecoded`, and lemmas that turn a
`BytesAt` span into a successful run of the extracted readers (`reader.read_u32_leb`,
`code.read_op`, `code.take_index`, `code.read_memarg`, ...).
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.Scalar

/-- A byte interval splits at any boundary of its bytes. -/
theorem BytesAt.split {data start next first rest}
    (h : BytesAt data start (first ++ rest) next) :
    ∃ middle, BytesAt data start first middle ∧ BytesAt data middle rest next := by
  have hlen := h.length
  simp only [List.length_append] at hlen
  let middle : Usize := Usize.ofNatCore (start.val + first.length)
    (by have := next.hmax; omega)
  have hm : middle.val = start.val + first.length := by simp [middle]
  have ht : data.val.drop middle.val = rest ++ data.val.drop next.val := by
    have hh := congrArg (List.drop first.length) h.suffix
    simpa [hm, List.drop_drop, List.drop_append, Nat.add_comm] using hh
  refine ⟨middle, ⟨?_, hm, by have := h.bound; omega⟩, ⟨ht, by omega, h.bound⟩⟩
  simpa [ht, List.append_assoc] using h.suffix

/-- An empty byte list occupies no input. -/
theorem BytesAt.empty {data start next} (h : BytesAt data start [] next) : next = start := by
  apply UScalar.eq_of_val_eq
  simpa using h.length

/-- A one-byte interval is the byte at the cursor. -/
theorem BytesAt.single {data start next byte} (h : BytesAt data start [byte] next) :
    ∃ hp : start.val < data.length, data.val[start.val] = byte ∧ next.val = start.val + 1 := by
  have hn : next.val = start.val + 1 := by simpa using h.length
  have hp : start.val < data.length := by have := h.bound; omega
  have hs := h.suffix
  rw [List.drop_eq_getElem_cons hp] at hs
  exact ⟨hp, (List.cons.inj hs).1, hn⟩

/-- `reader.read_byte` returns the byte of a one-byte interval. -/
theorem BytesAt.read_byte {data start next byte} (h : BytesAt data start [byte] next) :
    reader.read_byte data start = .ok (.Ok (byte, next)) := by
  obtain ⟨hp, hb, hn⟩ := h.single
  obtain ⟨_, hr, p, rfl, hp'⟩ := WP.spec_imp_exists (reader.read_byte.spec data start hp)
  have heq : p = next := UScalar.eq_of_val_eq (hp'.trans hn.symm)
  simpa [hb, heq] using hr

/-- A span with a `Binary.Leb128.Encoding` is a `Binary.Leb128.Decoded` span. -/
theorem BytesAt.u32_decoded {data start next bytes} (value : U32)
    (h : BytesAt data start bytes next) (he : Binary.Leb128.Encoding bytes value.val) :
    Binary.Leb128.Decoded data start value next := ⟨bytes, h.suffix, h.length, h.bound, he⟩

/-- `reader.read_u32_leb` reads an unsigned LEB128 span. -/
theorem BytesAt.read_u32 {data start next bytes} (value : U32)
    (h : BytesAt data start bytes next) (he : Binary.Leb128.Encoding bytes value.val) :
    reader.read_u32_leb data start = .ok (.Ok (value, next)) :=
  reader.read_u32_leb.complete data start value next (h.u32_decoded value he)

/-- `reader.read_f64_bits` reads an eight-byte span. -/
theorem BytesAt.read_f64 {data start next bytes} (bits : U64)
    (h : BytesAt data start bytes next) (he : Binary.FloatBits.Encoding 8 bytes bits.val) :
    reader.read_f64_bits data start = .ok (.Ok (bits, next)) :=
  reader.read_f64_bits.complete data start bits next
    ⟨bytes, h.suffix, by simpa [he.1] using h.length, h.bound, he⟩

/-- `code.take_index` reads an index span. -/
theorem BytesAt.take_index {data next bytes} (st : code.OpIterState) (idx : U32)
    (h : BytesAt data st.pos bytes next) (he : Binary.Leb128.Encoding bytes idx.val) :
    code.take_index st data = .ok (.Ok idx, { st with pos := next }) := by
  simp [code.take_index, h.read_u32 idx he, core.result.Result.Insts.CoreOpsTry.branch]

/-- `code.read_memarg` reads an alignment span followed by an offset span. -/
theorem BytesAt.read_memarg {data next alignment offset} (st : code.OpIterState)
    (arg : code.MemArg) (h : BytesAt data st.pos (alignment ++ offset) next)
    (ha : Binary.Leb128.Encoding alignment arg.align.val) (ho : Binary.Leb128.Encoding offset arg.offset.val) :
    code.read_memarg st data = .ok (.Ok arg, { st with pos := next }) := by
  obtain ⟨middle, hfirst, hrest⟩ := h.split
  have hr := hfirst.read_u32 arg.align ha
  have hr' := hrest.read_u32 arg.offset ho
  cases arg
  simp_all [code.read_memarg, core.result.Result.Insts.CoreOpsTry.branch]

end Itasca.Body.Scalar

namespace Itasca.Body.BrTable

/-- Label runs compose. -/
theorem LabelsDecoded.append {data start middle next first rest}
    (hfirst : LabelsDecoded data start first middle)
    (hrest : LabelsDecoded data middle rest next) :
    LabelsDecoded data start (first ++ rest) next := by
  induction hrest with
  | nil => simpa using hfirst
  | snoc _ hd ih => simpa [List.append_assoc] using LabelsDecoded.snoc ih hd

private theorem labels_split {data start depths next} (h : LabelsDecoded data start depths next)
    (first rest : List U32) (heq : depths = first ++ rest) :
    ∃ middle, LabelsDecoded data start first middle ∧ LabelsDecoded data middle rest next := by
  induction h generalizing first rest with
  | nil =>
      have he : first = [] ∧ rest = [] := by simpa using heq.symm
      rcases he with ⟨rfl, rfl⟩
      exact ⟨start, .nil, .nil⟩
  | @snoc depths pos next depth hprefix hlast ih =>
      cases rest using List.reverseRecOn with
      | nil =>
          have hf : first = depths ++ [depth] := by simpa using heq.symm
          subst first
          exact ⟨next, .snoc hprefix hlast, .nil⟩
      | append_singleton rest last =>
          have heq' : depths ++ [depth] = (first ++ rest) ++ [last] := by
            simpa [List.append_assoc] using heq
          have ht : depth = last := by
            have := congrArg List.getLast? heq'
            simpa using this
          subst last
          obtain ⟨middle, hf, hr⟩ := ih first rest (List.append_cancel_right heq')
          exact ⟨middle, hf, .snoc hr hlast⟩

private theorem labels_empty {data start depths next}
    (h : LabelsDecoded data start depths next) (he : depths = []) : next = start := by
  cases h with
  | nil => rfl
  | snoc => simp at he

private theorem labels_single {data start next depth}
    (h : LabelsDecoded data start [depth] next) : Binary.Leb128.Decoded data start depth next := by
  generalize he : [depth] = depths at h
  cases h with
  | nil => simp at he
  | @snoc depths pos next last hp hl =>
      have hlen := congrArg List.length he
      simp only [List.length_cons, List.length_nil, List.length_append] at hlen
      have ht : depths = [] := List.length_eq_zero_iff.mp (by omega)
      have heq : last = depth := by simpa [ht] using he.symm
      have hpos := labels_empty hp ht
      simpa [heq, hpos] using hl

/-- A nonempty label run is its first label followed by the rest. -/
theorem LabelsDecoded.cons_iff {data start next depth depths} :
    LabelsDecoded data start (depth :: depths) next ↔
      ∃ middle, Binary.Leb128.Decoded data start depth middle ∧ LabelsDecoded data middle depths next := by
  constructor
  · intro h
    obtain ⟨middle, hh, ht⟩ := labels_split h [depth] depths rfl
    exact ⟨middle, labels_single hh, ht⟩
  · rintro ⟨middle, hh, ht⟩
    exact LabelsDecoded.append (.snoc .nil hh) ht

end Itasca.Body.BrTable

namespace Itasca.Body.Scalar

/-- An `IndicesEncoding` over a byte span gives a run of decoded labels. -/
theorem IndicesEncoding.decoded {indices bytes} (he : IndicesEncoding indices bytes)
    {data start next} (h : BytesAt data start bytes next) :
    Body.BrTable.LabelsDecoded data start indices next := by
  induction he generalizing start with
  | nil => have hn := h.empty; subst next; exact .nil
  | cons hidx _ ih =>
      obtain ⟨middle, hfirst, hrest⟩ := h.split
      have hhead := Body.BrTable.LabelsDecoded.snoc .nil (hfirst.u32_decoded _ hidx)
      simpa using hhead.append (ih hrest)

/-- The count, entries and default label of a `br_table` immediate give a `Body.BrTable.Decoded`. The
count's `u32` range follows from its own encoding. -/
theorem BytesAt.br_table_decoded {data start next count entries final}
    (indices : List U32) (default : U32)
    (h : BytesAt data start (count ++ entries ++ final) next)
    (hc : Binary.Leb128.Encoding count indices.length) (he : IndicesEncoding indices entries)
    (hf : Binary.Leb128.Encoding final default.val) :
    Body.BrTable.Decoded data start indices default next := by
  obtain ⟨last, hprefix, hfinal⟩ := h.split
  obtain ⟨first, hcount, hentries⟩ := hprefix.split
  let n : U32 := U32.ofNatCore indices.length (by simpa using hc.value_lt)
  have hn : n.val = indices.length := by simp [n]
  exact ⟨n, first, last, hcount.u32_decoded n (by simpa [hn] using hc), hn.symm,
    he.decoded hentries, hfinal.u32_decoded default hf⟩

/-- A consumed span splits at any token boundary. -/
theorem Consumed.split_eq {data start tokens next} (h : Consumed data start tokens next)
    (first rest : List Token) (heq : tokens = first ++ rest) :
    ∃ middle, Consumed data start first middle ∧ Consumed data middle rest next := by
  induction h generalizing first rest with
  | nil hb =>
      have hempty : first = [] ∧ rest = [] := by simpa using heq.symm
      rcases hempty with ⟨rfl, rfl⟩
      exact ⟨start, .nil start hb, .nil start hb⟩
  | @snoc tokens pos token next hprefix hlast ih =>
      cases rest using List.reverseRecOn with
      | nil =>
          have hf : first = tokens ++ [token] := by simpa using heq.symm
          subst first
          exact ⟨next, .snoc hprefix hlast, .nil next hlast.span.2⟩
      | append_singleton rest last =>
          have heq' : tokens ++ [token] = (first ++ rest) ++ [last] := by
            simpa [List.append_assoc] using heq
          have ht : token = last := by
            have := congrArg List.getLast? heq'
            simpa using this
          subst last
          have hp : tokens = first ++ rest := List.append_cancel_right heq'
          obtain ⟨middle, hf, hr⟩ := ih first rest hp
          exact ⟨middle, hf, .snoc hr hlast⟩

/-- A consumed span of a concatenation splits into consecutive spans. -/
theorem Consumed.split {data start next first rest}
    (h : Consumed data start (first ++ rest) next) :
    ∃ middle, Consumed data start first middle ∧ Consumed data middle rest next :=
  h.split_eq first rest rfl

/-- An empty token list leaves the cursor in place. -/
theorem Consumed.empty_eq {data start tokens next}
    (h : Consumed data start tokens next) (he : tokens = []) : next = start := by
  cases h with
  | nil => rfl
  | snoc => simp at he

/-- A consumed span of one token is an `At`. -/
theorem Consumed.single {data start next token}
    (h : Consumed data start [token] next) : At data start token next := by
  generalize he : [token] = tokens at h
  cases h with
  | nil => simp at he
  | @snoc tokens pos last next hp hl =>
      have hlen := congrArg List.length he
      simp only [List.length_cons, List.length_nil, List.length_append] at hlen
      have ht : tokens = [] := List.length_eq_zero_iff.mp (by omega)
      have heq : last = token := by simpa [ht] using he.symm
      have hpos := hp.empty_eq ht
      simpa [heq, hpos] using hl

/-- A nonempty consumed span is its first token followed by the rest. -/
theorem Consumed.cons_iff {data start next token tokens} :
    Consumed data start (token :: tokens) next ↔
      ∃ middle, At data start token middle ∧ Consumed data middle tokens next := by
  constructor
  · intro h
    obtain ⟨middle, hh, ht⟩ := h.split_eq [token] tokens rfl
    exact ⟨middle, hh.single, ht⟩
  · rintro ⟨middle, hh, ht⟩
    have hb : start.val ≤ data.length := by have := hh.span; omega
    exact Consumed.append (.snoc (.nil start hb) hh) ht

end Itasca.Body.Scalar

end

end
