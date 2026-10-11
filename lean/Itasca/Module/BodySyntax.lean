import Itasca.Module.ModuleNameFacts
import Itasca.Profile.CodeEntry

open Aeneas Aeneas.Std

namespace Itasca.BodyContext

/-- Only segment-indexed instructions are excluded here; recursive structure
is retained so deleting module segment contexts is justified syntactically. -/
def PlainSegmentFree : instr → Prop
  | .BLOCK _ _ | .LOOP _ _ | .IFELSE _ _ _ => False
  | .TABLE_INIT _ _ | .ELEM_DROP _ | .MEMORY_INIT _ | .DATA_DROP _ => False
  | _ => True

inductive SegmentFree : instr → Prop where
  | plain (op : instr) : PlainSegmentFree op → SegmentFree op
  | block (bt : blocktype) (ops : List instr) :
      Forall SegmentFree ops → SegmentFree (.BLOCK bt ops)
  | loop (bt : blocktype) (ops : List instr) :
      Forall SegmentFree ops → SegmentFree (.LOOP bt ops)
  | ifElse (bt : blocktype) (yes no : List instr) :
      Forall SegmentFree yes → Forall SegmentFree no → SegmentFree (.IFELSE bt yes no)

@[simp] theorem SegmentFree.block_iff {bt ops} :
    SegmentFree (.BLOCK bt ops) ↔ Forall SegmentFree ops := by
  constructor
  · intro h; cases h with | plain _ h => exact False.elim h | block _ _ h => exact h
  · exact .block _ _

@[simp] theorem SegmentFree.loop_iff {bt ops} :
    SegmentFree (.LOOP bt ops) ↔ Forall SegmentFree ops := by
  constructor
  · intro h; cases h with | plain _ h => exact False.elim h | loop _ _ h => exact h
  · exact .loop _ _

@[simp] theorem SegmentFree.if_iff {bt yes no} :
    SegmentFree (.IFELSE bt yes no) ↔ Forall SegmentFree yes ∧ Forall SegmentFree no := by
  constructor
  · intro h; cases h with | plain _ h => exact False.elim h | ifElse _ _ _ hy hn => exact ⟨hy, hn⟩
  · rintro ⟨hy, hn⟩; exact .ifElse _ _ _ hy hn

@[simp] theorem SegmentFree.not_table_init {a b} : ¬ SegmentFree (.TABLE_INIT a b) := by
  intro h; cases h with | plain _ h => exact h
@[simp] theorem SegmentFree.not_elem_drop {a} : ¬ SegmentFree (.ELEM_DROP a) := by
  intro h; cases h with | plain _ h => exact h
@[simp] theorem SegmentFree.not_memory_init {a} : ¬ SegmentFree (.MEMORY_INIT a) := by
  intro h; cases h with | plain _ h => exact h
@[simp] theorem SegmentFree.not_data_drop {a} : ¬ SegmentFree (.DATA_DROP a) := by
  intro h; cases h with | plain _ h => exact h

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem numeric_segmentFree (opcode : U8) (op : Numeric.Operation)
    (hmap : Numeric.opcodeMeaning opcode = some op) : SegmentFree op.instruction := by
  unfold Numeric.opcodeMeaning at hmap
  split at hmap <;> simp only [Option.some.injEq, reduceCtorEq] at hmap
  all_goals first | contradiction | subst op; exact .plain _ trivial

set_option maxRecDepth 4096 in
theorem memory_segmentFree (opcode : U8) (op : MemoryMeaning.Operation)
    (hmap : MemoryMeaning.opcodeMeaning opcode = some op) (arg : code.MemArg) :
    SegmentFree (op.op arg) := by
  unfold MemoryMeaning.opcodeMeaning at hmap
  split at hmap <;> simp only [Option.some.injEq, reduceCtorEq] at hmap
  all_goals first | contradiction | subst op; exact .plain _ trivial

def TokenSegmentFree : Wasm.Token → Prop
  | .plain op => SegmentFree op
  | _ => True

theorem immediate_segmentFree {opcode token bytes} (h : Wasm.Immediate opcode token bytes) :
    TokenSegmentFree token := by
  cases h
  case memory => exact memory_segmentFree _ _ (by assumption) _
  case numeric => exact numeric_segmentFree _ _ (by assumption)
  all_goals first | trivial | exact .plain _ trivial

theorem token_segmentFree {token bytes} (h : Wasm.TokenEncoding token bytes) :
    TokenSegmentFree token := by
  obtain ⟨_, _, _, h⟩ := h
  exact immediate_segmentFree h

theorem emits_segmentFree {tokens ops} (h : Wasm.Emits tokens ops)
    (ht : Forall TokenSegmentFree tokens) : Forall SegmentFree ops := by
  induction h with
  | nil => simp [Forall]
  | simple he hs ih =>
    have hp := ih (fun t hm => ht t (List.mem_append_left _ hm))
    cases hs with
    | plain op hw =>
      have hl := ht _ (List.mem_append_right _ (List.mem_singleton_self _))
      simpa [Forall, or_imp, forall_and, TokenSegmentFree] using And.intro hp hl
  | block bt he hb ih ihb =>
    have hp := ih (fun t hm => ht t (by simp [hm]))
    have hc := ihb (fun t hm => ht t (by simp [hm]))
    simpa [Forall, or_imp, forall_and] using And.intro hp (SegmentFree.block (Control.blockType bt) _ hc)
  | loop bt he hb ih ihb =>
    have hp := ih (fun t hm => ht t (by simp [hm]))
    have hc := ihb (fun t hm => ht t (by simp [hm]))
    simpa [Forall, or_imp, forall_and] using And.intro hp (SegmentFree.loop (Control.blockType bt) _ hc)
  | ifElse bt he hy hn ih ihy ihn =>
    have hp := ih (fun t hm => ht t (by simp [hm]))
    have hy := ihy (fun t hm => ht t (by simp [hm]))
    have hn := ihn (fun t hm => ht t (by simp [hm]))
    simpa [Forall, or_imp, forall_and] using And.intro hp (SegmentFree.ifElse (Control.blockType bt) _ _ hy hn)
  | ifEnd bt he hb ih ihb =>
    have hp := ih (fun t hm => ht t (by simp [hm]))
    have hc := ihb (fun t hm => ht t (by simp [hm]))
    simpa [Forall, or_imp, forall_and] using And.intro hp
      (SegmentFree.ifElse (Control.blockType bt) _ [] hc (by simp [Forall]))

theorem body_segmentFree {ops bytes} (h : ModuleBinary.BodyEncoding ops bytes) :
    Forall SegmentFree ops := by
  obtain ⟨tokens, htokens, inner, rfl, hemits⟩ := h
  apply emits_segmentFree hemits
  intro token ht
  have hm : token ∈ inner ++ [.end_] := List.mem_append_left _ ht
  obtain ⟨bs, he⟩ := htokens.member hm
  exact token_segmentFree he

end Itasca.BodyContext

namespace Itasca.Profile

theorem BodyBytes.segmentFree {ops bytes} (h : BodyBytes .Wasm1 ops bytes) :
    Forall BodyContext.SegmentFree ops :=
  BodyContext.body_segmentFree h

end Itasca.Profile
