import Itasca.Binary.CoreSyntax
import Itasca.Binary.SignedLeb

open Aeneas Aeneas.Std

namespace Itasca.Core

/-- Local transcription of the Wasm 1.0 immediates in the core profile.
The current SpecTec Lean backend does not emit binary-format judgments. -/
inductive Immediate : Token → List U8 → Prop where
  | nop : Immediate .nop []
  | unreachable : Immediate .unreachable []
  | drop : Immediate .drop []
  | i32Add : Immediate .i32Add []
  | i32Const (v : I32) {bytes} : SignedLeb.Encoding bytes v.val →
      Immediate (.i32Const v) bytes
  | block (bt : code.BlockType) : Immediate (.block bt) [Control.blockByte bt]
  | loop (bt : code.BlockType) : Immediate (.loop bt) [Control.blockByte bt]
  | if_ (bt : code.BlockType) : Immediate (.if_ bt) [Control.blockByte bt]
  | else_ : Immediate .else_ []
  | end_ : Immediate .end_ []
  | br (d : U32) {bytes} : Leb128.Encoding bytes d.val → Immediate (.br d) bytes
  | brIf (d : U32) {bytes} : Leb128.Encoding bytes d.val → Immediate (.brIf d) bytes
  | return_ : Immediate .return_ []

def TokenEncoding (token : Token) (bytes : List U8) : Prop :=
  ∃ immediate, bytes = token.opcode :: immediate ∧ Immediate token immediate

/-- One encoded token occupies exactly this cursor interval. -/
def At (data : Slice U8) (start : Usize) (token : Token) (next : Usize) : Prop :=
  ∃ immediate, Immediate token immediate ∧
    data.val.drop start.val = token.opcode :: (immediate ++ data.val.drop next.val) ∧
    next.val = start.val + 1 + immediate.length ∧ next.val ≤ data.length

/-- All bytes from this cursor to EOF are core-profile tokens. The relation
does not assume balanced control flow, valid labels, or operand typing. -/
inductive Rest (data : Slice U8) : Usize → List Token → Prop where
  | nil (pos : Usize) : pos.val = data.length → Rest data pos []
  | cons {pos next token tokens} : At data pos token next →
      Rest data next tokens → Rest data pos (token :: tokens)

def BodyEncoding (data : Slice U8) (ops : List instr) : Prop :=
  ∃ tokens, Rest data 0#usize tokens ∧ BodyTokens tokens ops

theorem At.span {data start token next} (h : At data start token next) :
    start.val < next.val ∧ next.val ≤ data.length := by
  obtain ⟨imm, _, _, hn, hb⟩ := h
  exact ⟨by omega, hb⟩

theorem At.opcode {data start token next} (h : At data start token next) :
    ∃ hp : start.val < data.length, data.val[start.val] = token.opcode := by
  have hp : start.val < data.length := Nat.lt_of_lt_of_le h.span.1 h.span.2
  obtain ⟨imm, _, heq, _, _⟩ := h
  refine ⟨hp, ?_⟩
  rw [List.drop_eq_getElem_cons hp] at heq
  exact (List.cons.inj heq).1

/-- After consuming the opcode, the immediate relation still describes the
exact unread bytes, including the unchanged suffix after the token. -/
theorem At.immediate {data start token next} (h : At data start token next)
    (p : Usize) (hp : p.val = start.val + 1) :
    ∃ imm, Immediate token imm ∧
      data.val.drop p.val = imm ++ data.val.drop next.val ∧
      next.val = p.val + imm.length ∧ next.val ≤ data.length := by
  have hbound : start.val < data.length := Nat.lt_of_lt_of_le h.span.1 h.span.2
  obtain ⟨imm, hi, heq, hn, hb⟩ := h
  rw [List.drop_eq_getElem_cons hbound] at heq
  refine ⟨imm, hi, ?_, by omega, hb⟩
  simpa only [hp] using (List.cons.inj heq).2

theorem Rest.bound {data pos tokens} (h : Rest data pos tokens) : pos.val ≤ data.length := by
  cases h with
  | nil _ heq => omega
  | cons ha _ => exact Nat.le_of_lt (Nat.lt_of_lt_of_le ha.span.1 ha.span.2)

theorem Rest.empty_iff {data pos tokens} (h : Rest data pos tokens) :
    tokens = [] ↔ pos.val = data.length := by
  cases h with
  | nil _ hp => simp [hp]
  | cons ha _ =>
      have := ha.span
      simp only [List.cons_ne_nil, false_iff]
      omega

end Itasca.Core

namespace Itasca.Core

/-- These tokens consist only of their opcode byte. -/
def Token.noImmediate : Token → Bool
  | .nop | .unreachable | .drop | .i32Add | .else_ | .end_ | .return_ => true
  | _ => false

/-- A token without an immediate ends at the cursor just after its opcode. -/
theorem At.no_immediate {data start token next} (h : At data start token next)
    (p : Usize) (hp : p.val = start.val + 1) (hplain : token.noImmediate = true) : next = p := by
  obtain ⟨imm, hi, _, hn, _⟩ := h.immediate p hp
  apply UScalar.eq_of_val_eq
  cases hi <;> simp_all [Token.noImmediate]

/-- The byte relation identifies the exact signed value returned after the opcode. -/
theorem At.read_i32_const {data start next} {value : I32}
    (h : At data start (.i32Const value) next) (p : Usize) (hp : p.val = start.val + 1) :
    reader.read_s32_leb data p = .ok (.Ok (value, next)) := by
  obtain ⟨imm, hi, hbytes, hnext, hbound⟩ := h.immediate p hp
  cases hi with
  | i32Const _ hencoding =>
    exact reader.read_s32_leb.complete data p value next ⟨_, hbytes, hnext, hbound, hencoding⟩

theorem At.read_br {data start next} {depth : U32}
    (h : At data start (.br depth) next) (p : Usize) (hp : p.val = start.val + 1) :
    reader.read_u32_leb data p = .ok (.Ok (depth, next)) := by
  obtain ⟨imm, hi, hbytes, hnext, hbound⟩ := h.immediate p hp
  cases hi with
  | br _ hencoding =>
    exact reader.read_u32_leb.complete data p depth next ⟨_, hbytes, hnext, hbound, hencoding⟩

theorem At.read_brIf {data start next} {depth : U32}
    (h : At data start (.brIf depth) next) (p : Usize) (hp : p.val = start.val + 1) :
    reader.read_u32_leb data p = .ok (.Ok (depth, next)) := by
  obtain ⟨imm, hi, hbytes, hnext, hbound⟩ := h.immediate p hp
  cases hi with
  | brIf _ hencoding =>
    exact reader.read_u32_leb.complete data p depth next ⟨_, hbytes, hnext, hbound, hencoding⟩

private theorem read_block_type_of_byte (data : Slice U8) (p next : Usize) (bt : code.BlockType)
    (hbytes : data.val.drop p.val = Control.blockByte bt :: data.val.drop next.val)
    (hnext : next.val = p.val + 1) (hbound : next.val ≤ data.length) :
    code.read_block_type data p = .ok (.Ok (bt, next)) := by
  have hp : p.val < data.length := by omega
  rw [List.drop_eq_getElem_cons hp] at hbytes
  have hbyte := (List.cons.inj hbytes).1
  obtain ⟨_, hr, q, rfl, hq⟩ := WP.spec_imp_exists (code.read_block_type.spec data p bt hp hbyte)
  have heq : q = next := UScalar.eq_of_val_eq (by omega)
  simpa [heq] using hr

theorem At.read_block {data start next} {bt : code.BlockType}
    (h : At data start (.block bt) next) (p : Usize) (hp : p.val = start.val + 1) :
    code.read_block_type data p = .ok (.Ok (bt, next)) := by
  obtain ⟨imm, hi, hbytes, hnext, hbound⟩ := h.immediate p hp
  cases hi
  exact read_block_type_of_byte data p next bt (by simpa using hbytes) (by simpa using hnext) hbound

theorem At.read_loop {data start next} {bt : code.BlockType}
    (h : At data start (.loop bt) next) (p : Usize) (hp : p.val = start.val + 1) :
    code.read_block_type data p = .ok (.Ok (bt, next)) := by
  obtain ⟨imm, hi, hbytes, hnext, hbound⟩ := h.immediate p hp
  cases hi
  exact read_block_type_of_byte data p next bt (by simpa using hbytes) (by simpa using hnext) hbound

theorem At.read_if {data start next} {bt : code.BlockType}
    (h : At data start (.if_ bt) next) (p : Usize) (hp : p.val = start.val + 1) :
    code.read_block_type data p = .ok (.Ok (bt, next)) := by
  obtain ⟨imm, hi, hbytes, hnext, hbound⟩ := h.immediate p hp
  cases hi
  exact read_block_type_of_byte data p next bt (by simpa using hbytes) (by simpa using hnext) hbound

/-- Expose the next token boundary without assuming anything about control or operand validity. -/
theorem Rest.cons_iff {data pos token tokens} : Rest data pos (token :: tokens) ↔
    ∃ next, At data pos token next ∧ Rest data next tokens := by
  constructor
  · intro h
    cases h with
    | cons ha ht => exact ⟨_, ha, ht⟩
  · rintro ⟨next, ha, ht⟩
    exact .cons ha ht

end Itasca.Core
