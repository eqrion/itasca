import Itasca.Binary.Wasm2.Simd
import Itasca.Binary.Wasm2.References
import Itasca.Binary.Wasm2.Bulk
import Itasca.Binary.Wasm2.NumericExtensions
import Itasca.Binary.Wasm2.Syntax
import Itasca.Binary.Wasm2.BlockType
import Itasca.Binary.Wasm1.Encoding

/-!
# Wasm 2.0 instruction binary grammar

The handwritten binary grammar of Wasm 2.0 instructions. `Immediate` relates an opcode byte to a
token and its immediate bytes, reusing the Wasm 1.0 plain instructions and adding sign extension,
saturating truncation, reference, bulk memory, SIMD and structured control with `BlockEncoding`
block types. `At`, `Consumed` and `BodyEncoding` place tokens, token runs and complete bodies in a
byte slice, as in `Binary/Wasm1/Encoding`. The grammar does not mention validation.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- A block type as a literal tag byte or a nonnegative signed 33-bit type index. -/
def BlockEncoding (bt : signature.BlockType) (bytes : List U8) : Prop :=
  match bt with
  | .Empty => bytes = [64#u8]
  | .Value t => bytes = [valueByte t]
  | .TypeIndex i => SignedLeb33.Encoding bytes i.val

/-- `BlockDecoded` at a cursor is a `BlockEncoding` over an interval of the input. -/
theorem blockDecoded_iff {data pos bt next} :
    BlockDecoded data pos bt next ↔
      ∃ bytes, BlockEncoding bt bytes ∧ Wasm1.BytesAt data pos bytes next := by
  cases bt with
  | Empty | Value _ =>
    constructor
    · rintro ⟨hp, hv, hn⟩
      exact ⟨_, rfl, .byte data pos next _ hp hv hn⟩
    · rintro ⟨bytes, rfl, hs⟩
      have hn : next.val = pos.val + 1 := by simpa using hs.length
      have hp : pos.val < data.length := by have := hs.bound; omega
      refine ⟨hp, ?_, hn⟩
      have hh := congrArg List.head? hs.suffix
      simpa only [List.drop_eq_getElem_cons hp, List.singleton_append,
        List.head?_cons, Option.some.injEq] using hh
  | TypeIndex i =>
    exact ⟨fun ⟨bs, hs, hl, hb, he⟩ => ⟨bs, he, hs, hl, hb⟩,
      fun ⟨bs, he, hs, hl, hb⟩ => ⟨bs, hs, hl, hb, he⟩⟩

/-- The immediate bytes that follow an opcode byte for a Wasm 2.0 token. Plain Wasm 1.0 leaves are
reused, but structured instructions take `BlockEncoding` block types. -/
inductive Immediate : U8 → Token → List U8 → Prop where
  | plain {opcode op bytes} : Wasm1.Immediate opcode (.plain op) bytes →
      Immediate opcode (.plain op) bytes
  | signExtension (opcode : U8) (operation : Numeric.Operation) :
      NumericExtensions.signMeaning opcode = some operation →
      Immediate opcode (.plain operation.instruction) []
  | saturating (subopcode : U32) (operation : Numeric.Operation) {bytes} :
      NumericExtensions.saturatingMeaning subopcode = some operation →
      Leb128.Encoding bytes subopcode.val → Immediate 0xFC#u8 (.plain operation.instruction) bytes
  | reference {opcode op bytes} : ReferencesBinary.Immediate opcode op bytes →
      Immediate opcode (.plain op) bytes
  | bulk (subopcode : U32) {prefixBytes op bytes} : Leb128.Encoding prefixBytes subopcode.val →
      BulkBinary.Immediate subopcode op bytes → Immediate 0xfc#u8 (.plain op) (prefixBytes ++ bytes)
  | simd (subopcode : U32) {prefixBytes op bytes} : Leb128.Encoding prefixBytes subopcode.val →
      Simd.Immediate subopcode op bytes → Immediate 0xfd#u8 (.plain op) (prefixBytes ++ bytes)
  | block {bt bytes} : BlockEncoding bt bytes → Immediate 0x02#u8 (.block bt) bytes
  | loop {bt bytes} : BlockEncoding bt bytes → Immediate 0x03#u8 (.loop bt) bytes
  | if_ {bt bytes} : BlockEncoding bt bytes → Immediate 0x04#u8 (.if_ bt) bytes
  | else_ : Immediate 0x05#u8 .else_ []
  | end_ : Immediate 0x0B#u8 .end_ []

/-- A token as its opcode byte followed by its immediate bytes. -/
def TokenEncoding (token : Token) (bytes : List U8) : Prop :=
  ∃ opcode immediate, bytes = opcode :: immediate ∧ Immediate opcode token immediate

/-- A token is encoded by the interval from `start` to `next`. The suffix is unrestricted. -/
def At (data : Slice U8) (start : Usize) (token : Token) (next : Usize) : Prop :=
  ∃ bytes, TokenEncoding token bytes ∧ Wasm1.BytesAt data start bytes next

/-- The tokens read from `start` to the cursor, accumulated one `At` step at a time. Unread bytes
are unconstrained. -/
inductive Consumed (data : Slice U8) : Usize → List Token → Usize → Prop where
  | nil (pos : Usize) (bound : pos.val ≤ data.length) : Consumed data pos [] pos
  | snoc {start tokens pos token next} : Consumed data start tokens pos →
      At data pos token next → Consumed data start (tokens ++ [token]) next

/-- A complete function body: the tokens read from offset 0 reach the end of `data`, and end with
the final `end`. -/
def BodyEncoding (data : Slice U8) (ops : List instr) : Prop :=
  ∃ tokens next, Consumed data 0#usize tokens next ∧
    next.val = data.length ∧ BodyTokens tokens ops

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
    (himmediate : Immediate opcode token immediate)
    (hspan : Wasm1.BytesAt data pos immediate next) : At data start token next := by
  exact ⟨opcode :: immediate, ⟨opcode, immediate, rfl, himmediate⟩,
    by simpa using (Wasm1.BytesAt.byte data start pos opcode hstart hbyte hpos).append hspan⟩

/-- A structured instruction header token from a decoded block type. -/
theorem At.of_block_type {data start pos next opcode token} (bt : signature.BlockType)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = opcode)
    (hpos : pos.val = start.val + 1)
    (himm : ∀ bytes, BlockEncoding bt bytes → Immediate opcode token bytes)
    (hdecoded : BlockDecoded data pos bt next) : At data start token next := by
  obtain ⟨bytes, he, hs⟩ := blockDecoded_iff.mp hdecoded
  exact .of_immediate hstart hbyte hpos (himm bytes he) hs

/-- A Wasm 1.0 plain token is a Wasm 2.0 token. -/
theorem At.plain {data start op next} (h : Wasm1.At data start (.plain op) next) :
    At data start (.plain op) next := by
  obtain ⟨bs, ⟨opcode, imm, rfl, hi⟩, hs⟩ := h
  exact ⟨_, ⟨opcode, imm, rfl, .plain hi⟩, hs⟩

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

end Itasca.Wasm2
