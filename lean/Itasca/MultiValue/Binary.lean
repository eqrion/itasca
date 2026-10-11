import Itasca.MultiValue.Syntax
import Itasca.MultiValue.BlockDecode
import Itasca.Binary.WasmBinary

open Aeneas Aeneas.Std

namespace Itasca.MultiValue

/-- Literal block tags or a nonnegative signed s33 type index. This grammar
does not resolve indices, impose implementation limits, or run a reader. -/
def BlockEncoding (bt : signature.BlockType) (bytes : List U8) : Prop :=
  match bt with
  | .Empty => bytes = [64#u8]
  | .Value t => bytes = [valueByte t]
  | .TypeIndex i => SignedLeb33.Encoding bytes i.val

theorem blockDecoded_iff {data pos bt next} :
    BlockDecoded data pos bt next ↔
      ∃ bytes, BlockEncoding bt bytes ∧ Wasm.BytesAt data pos bytes next := by
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

/-- Shared leaf bytes plus multi-value structured control. Reusing only the
`plain` case excludes the old grammar's single-byte block restriction. -/
inductive Immediate : U8 → Token → List U8 → Prop where
  | plain {opcode op bytes} : Wasm.Immediate opcode (.plain op) bytes →
      Immediate opcode (.plain op) bytes
  | block {bt bytes} : BlockEncoding bt bytes → Immediate 0x02#u8 (.block bt) bytes
  | loop {bt bytes} : BlockEncoding bt bytes → Immediate 0x03#u8 (.loop bt) bytes
  | if_ {bt bytes} : BlockEncoding bt bytes → Immediate 0x04#u8 (.if_ bt) bytes
  | else_ : Immediate 0x05#u8 .else_ []
  | end_ : Immediate 0x0B#u8 .end_ []

def TokenEncoding (token : Token) (bytes : List U8) : Prop :=
  ∃ opcode immediate, bytes = opcode :: immediate ∧ Immediate opcode token immediate

def At (data : Slice U8) (start : Usize) (token : Token) (next : Usize) : Prop :=
  ∃ bytes, TokenEncoding token bytes ∧ Wasm.BytesAt data start bytes next

/-- Only the consumed prefix is constrained; unread bytes may be malformed. -/
inductive Consumed (data : Slice U8) : Usize → List Token → Usize → Prop where
  | nil (pos : Usize) (bound : pos.val ≤ data.length) : Consumed data pos [] pos
  | snoc {start tokens pos token next} : Consumed data start tokens pos →
      At data pos token next → Consumed data start (tokens ++ [token]) next

/-- Independent body encoding, with the function's final end and exact input
consumption. Other Wasm 2.0 instruction proposals are not included. -/
def BodyEncoding (data : Slice U8) (ops : List instr) : Prop :=
  ∃ tokens next, Consumed data 0#usize tokens next ∧
    next.val = data.length ∧ BodyTokens tokens ops

theorem At.span {data start token next} (h : At data start token next) :
    start.val < next.val ∧ next.val ≤ data.length := by
  obtain ⟨_, ⟨op, imm, rfl, _⟩, hs⟩ := h
  have := hs.length
  simp only [List.length_cons] at this
  exact ⟨by omega, hs.bound⟩

theorem At.of_immediate {data start pos next opcode token immediate}
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = opcode)
    (hpos : pos.val = start.val + 1)
    (himmediate : Immediate opcode token immediate)
    (hspan : Wasm.BytesAt data pos immediate next) : At data start token next := by
  exact ⟨opcode :: immediate, ⟨opcode, immediate, rfl, himmediate⟩,
    by simpa using (Wasm.BytesAt.byte data start pos opcode hstart hbyte hpos).append hspan⟩

theorem At.of_block_type {data start pos next opcode token} (bt : signature.BlockType)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = opcode)
    (hpos : pos.val = start.val + 1)
    (himm : ∀ bytes, BlockEncoding bt bytes → Immediate opcode token bytes)
    (hdecoded : BlockDecoded data pos bt next) : At data start token next := by
  obtain ⟨bytes, he, hs⟩ := blockDecoded_iff.mp hdecoded
  exact .of_immediate hstart hbyte hpos (himm bytes he) hs

theorem At.plain {data start op next} (h : Wasm.At data start (.plain op) next) :
    At data start (.plain op) next := by
  obtain ⟨bs, ⟨opcode, imm, rfl, hi⟩, hs⟩ := h
  exact ⟨_, ⟨opcode, imm, rfl, .plain hi⟩, hs⟩

theorem Consumed.span {data start tokens next} (h : Consumed data start tokens next) :
    start.val ≤ next.val ∧ next.val ≤ data.length := by
  induction h with
  | nil hb => exact ⟨Nat.le_refl _, hb⟩
  | snoc _ ha ih => have := ha.span; omega

theorem Consumed.append {data start middle next first rest}
    (hfirst : Consumed data start first middle) (hrest : Consumed data middle rest next) :
    Consumed data start (first ++ rest) next := by
  induction hrest with
  | nil _ => simpa using hfirst
  | snoc _ ha ih => simpa [List.append_assoc] using Consumed.snoc ih ha

theorem BodyEncoding.wellFormed {data ops} (h : BodyEncoding data ops) :
    Forall wf_instr ops := by
  obtain ⟨_, _, _, _, _, _, he⟩ := h
  exact he.wellFormed

end Itasca.MultiValue
