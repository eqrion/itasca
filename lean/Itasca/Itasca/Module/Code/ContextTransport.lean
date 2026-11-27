import Itasca.Spec.Typing
import Itasca.Support.Translation
import Itasca.Binary.ModuleUnique
import Itasca.Module.Definitions
import Itasca.Results.Definitions.Validation
import Itasca.Module.Readers.Syntax
import Itasca.Binary.Scalar.Encoding

open WebAssembly

/-!
Proofs for Module / Code.

This module collects ContextTransport, Locals.
Each section documents its contracts and consumers.
-/

/-! ## ContextTransport -/

section

/-!
# Function-body context transport

Frame contexts, segment spaces and instruction typing are transported between the
environment and complete source module. Data-use syntax controls when the data context can
be changed.
-/

/-! ## BodyContext -/

section

/-!
# Body typing under extended segment spaces

`instrs_extend` preserves generated instruction typing under prefix extension
of element/data spaces. `instrs_transport_extend` transports typing between
contexts sharing their other fields. `instrs_transport_of_no_data` permits an
unrelated data space when the instruction syntax uses no data index.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.Context

/-- The context `C` with its element and data segment spaces replaced and every other field
unchanged. -/
def segments (C : context) (elems : List elemtype) (datas : List datatype) : context :=
  { C with ELEMS := elems, DATAS := datas }

/-- Replacing the segment spaces keeps a context well formed. -/
theorem segments_wf {C : context} (h : wf_context C)
    (elems : List elemtype) (datas : List datatype) : wf_context (segments C elems datas) := by
  cases h
  constructor <;> assumption

/-- Block type typing does not depend on the segment spaces. -/
theorem blocktype_segments {C : context} {bt : blocktype} {ft : functype}
    (h : Blocktype_ok C bt ft) (elems : List elemtype) (datas : List datatype) :
    Blocktype_ok (segments C elems datas) bt ft := by
  cases h with
  | valtype ts hC hw => exact .valtype _ _ (segments_wf hC _ _) hw
  | typeidx x ins outs hi hx hC hw =>
    exact .typeidx _ _ _ _ hi hx (segments_wf hC _ _) hw

private theorem prefix_index {α : Type} [Inhabited α] {xs ys : List α}
    (h : xs.IsPrefix ys) {i : Nat} (hi : i < xs.length) :
    i < ys.length ∧ ys[i]! = xs[i]! := by
  have hj := Nat.lt_of_lt_of_le hi h.length_le
  exact ⟨hj, by rw [getElem!_pos ys i hj, getElem!_pos xs i hi]; exact (h.getElem hi).symm⟩

/-- Extending the segment index spaces by prefix extension preserves instruction sequence typing,
since every existing index keeps its type. -/
theorem instrs_extend {C : context} {ops : List instr} {ft : functype}
    (h : Instrs_ok C ops ft) :
    ∀ elems datas, C.ELEMS.IsPrefix elems → C.DATAS.IsPrefix datas →
      Instrs_ok (segments C elems datas) ops ft := by
  induction h using Instrs_ok.rec
    (motive_1 := fun C op ft _ => ∀ elems datas, C.ELEMS.IsPrefix elems → C.DATAS.IsPrefix datas →
      Instr_ok (segments C elems datas) op ft)
  case nop =>
    rename_i elems datas he hd
    apply Instr_ok.nop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case unreachable =>
    rename_i elems datas he hd
    apply Instr_ok.unreachable <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case drop =>
    rename_i elems datas he hd
    apply Instr_ok.drop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case select_expl =>
    rename_i elems datas he hd
    apply Instr_ok.select_expl <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case select_impl =>
    rename_i elems datas he hd
    apply Instr_ok.select_impl <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case block =>
    rename_i elems datas he hd
    apply Instr_ok.block <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
      | exact blocktype_segments (by assumption) _ _
      | (apply_assumption <;> assumption)
  case loop =>
    rename_i elems datas he hd
    apply Instr_ok.loop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
      | exact blocktype_segments (by assumption) _ _
      | (apply_assumption <;> assumption)
  case «if» =>
    rename_i elems datas he hd
    apply Instr_ok.«if» <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
      | exact blocktype_segments (by assumption) _ _
      | (apply_assumption <;> assumption)
  case br =>
    rename_i elems datas he hd
    apply Instr_ok.br <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case br_if =>
    rename_i elems datas he hd
    apply Instr_ok.br_if <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case br_table =>
    rename_i elems datas he hd
    apply Instr_ok.br_table <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case call =>
    rename_i elems datas he hd
    apply Instr_ok.call <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case call_indirect =>
    rename_i elems datas he hd
    apply Instr_ok.call_indirect <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case «return» =>
    rename_i elems datas he hd
    apply Instr_ok.«return» <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case const =>
    rename_i elems datas he hd
    apply Instr_ok.const <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case unop =>
    rename_i elems datas he hd
    apply Instr_ok.unop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case binop =>
    rename_i elems datas he hd
    apply Instr_ok.binop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case testop =>
    rename_i elems datas he hd
    apply Instr_ok.testop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case relop =>
    rename_i elems datas he hd
    apply Instr_ok.relop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case cvtop =>
    rename_i elems datas he hd
    apply Instr_ok.cvtop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case ref_null =>
    rename_i elems datas he hd
    apply Instr_ok.ref_null <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case ref_func =>
    rename_i elems datas he hd
    apply Instr_ok.ref_func <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case ref_is_null =>
    rename_i elems datas he hd
    apply Instr_ok.ref_is_null <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vconst =>
    rename_i elems datas he hd
    apply Instr_ok.vconst <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vvunop =>
    rename_i elems datas he hd
    apply Instr_ok.vvunop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vvbinop =>
    rename_i elems datas he hd
    apply Instr_ok.vvbinop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vvternop =>
    rename_i elems datas he hd
    apply Instr_ok.vvternop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vvtestop =>
    rename_i elems datas he hd
    apply Instr_ok.vvtestop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vunop =>
    rename_i elems datas he hd
    apply Instr_ok.vunop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vbinop =>
    rename_i elems datas he hd
    apply Instr_ok.vbinop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vtestop =>
    rename_i elems datas he hd
    apply Instr_ok.vtestop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vrelop =>
    rename_i elems datas he hd
    apply Instr_ok.vrelop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vshiftop =>
    rename_i elems datas he hd
    apply Instr_ok.vshiftop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vbitmask =>
    rename_i elems datas he hd
    apply Instr_ok.vbitmask <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vswizzle =>
    rename_i elems datas he hd
    apply Instr_ok.vswizzle <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vshuffle =>
    rename_i elems datas he hd
    apply Instr_ok.vshuffle <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vsplat =>
    rename_i elems datas he hd
    apply Instr_ok.vsplat <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vextract_lane =>
    rename_i elems datas he hd
    apply Instr_ok.vextract_lane <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vreplace_lane =>
    rename_i elems datas he hd
    apply Instr_ok.vreplace_lane <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vextunop =>
    rename_i elems datas he hd
    apply Instr_ok.vextunop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vextbinop =>
    rename_i elems datas he hd
    apply Instr_ok.vextbinop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vnarrow =>
    rename_i elems datas he hd
    apply Instr_ok.vnarrow <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vcvtop =>
    rename_i elems datas he hd
    apply Instr_ok.vcvtop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case local_get =>
    rename_i elems datas he hd
    apply Instr_ok.local_get <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case local_set =>
    rename_i elems datas he hd
    apply Instr_ok.local_set <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case local_tee =>
    rename_i elems datas he hd
    apply Instr_ok.local_tee <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case global_get =>
    rename_i elems datas he hd
    apply Instr_ok.global_get <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case global_set =>
    rename_i elems datas he hd
    apply Instr_ok.global_set <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case table_get =>
    rename_i elems datas he hd
    apply Instr_ok.table_get <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case table_set =>
    rename_i elems datas he hd
    apply Instr_ok.table_set <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case table_size =>
    rename_i elems datas he hd
    apply Instr_ok.table_size <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case table_grow =>
    rename_i elems datas he hd
    apply Instr_ok.table_grow <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case table_fill =>
    rename_i elems datas he hd
    apply Instr_ok.table_fill <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case table_copy =>
    rename_i elems datas he hd
    apply Instr_ok.table_copy <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case table_init C x y lim rt hti hte hei hee hw hop hlim elems datas he hd =>
    obtain ⟨hi, hx⟩ := prefix_index he hei
    exact .table_init _ x y lim rt hti hte hi (hx.trans hee)
      (segments_wf hw _ _) hop hlim
  case elem_drop C x rt hei hee hw hop elems datas he hd =>
    obtain ⟨hi, hx⟩ := prefix_index he hei
    exact .elem_drop _ x rt hi (hx.trans hee) (segments_wf hw _ _) hop
  case memory_size =>
    rename_i elems datas he hd
    apply Instr_ok.memory_size <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case memory_grow =>
    rename_i elems datas he hd
    apply Instr_ok.memory_grow <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case memory_fill =>
    rename_i elems datas he hd
    apply Instr_ok.memory_fill <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case memory_copy =>
    rename_i elems datas he hd
    apply Instr_ok.memory_copy <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case memory_init C x mt hmi hme hdi hde hw hmt hop elems datas he hd =>
    obtain ⟨hi, hx⟩ := prefix_index hd hdi
    exact .memory_init _ x mt hmi hme hi (hx.trans hde)
      (segments_wf hw _ _) hmt hop
  case data_drop C x hdi hde hw hop elems datas he hd =>
    obtain ⟨hi, hx⟩ := prefix_index hd hdi
    exact .data_drop _ x hi (hx.trans hde) (segments_wf hw _ _) hop
  case load_val =>
    rename_i elems datas he hd
    apply Instr_ok.load_val <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case load_pack =>
    rename_i elems datas he hd
    apply Instr_ok.load_pack <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case store_val =>
    rename_i elems datas he hd
    apply Instr_ok.store_val <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case store_pack =>
    rename_i elems datas he hd
    apply Instr_ok.store_pack <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vload_val =>
    rename_i elems datas he hd
    apply Instr_ok.vload_val <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vload_pack =>
    rename_i elems datas he hd
    apply Instr_ok.vload_pack <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vload_splat =>
    rename_i elems datas he hd
    apply Instr_ok.vload_splat <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vload_zero =>
    rename_i elems datas he hd
    apply Instr_ok.vload_zero <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vload_lane =>
    rename_i elems datas he hd
    apply Instr_ok.vload_lane <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vstore =>
    rename_i elems datas he hd
    apply Instr_ok.vstore <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vstore_lane =>
    rename_i elems datas he hd
    apply Instr_ok.vstore_lane <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case empty =>
    intros elems datas he hd
    apply Instrs_ok.empty
    exact segments_wf (by assumption) _ _
  case instr =>
    intros elems datas he hd
    apply Instrs_ok.instr <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
      | exact blocktype_segments (by assumption) _ _
      | (apply_assumption <;> assumption)
  case seq =>
    intros elems datas he hd
    apply Instrs_ok.seq <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
      | exact blocktype_segments (by assumption) _ _
      | (apply_assumption <;> assumption)
  case sub =>
    intros elems datas he hd
    apply Instrs_ok.sub <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
      | exact blocktype_segments (by assumption) _ _
      | (apply_assumption <;> assumption)
  case frame =>
    intros elems datas he hd
    apply Instrs_ok.frame <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
      | exact blocktype_segments (by assumption) _ _
      | (apply_assumption <;> assumption)

/-- Two contexts agree on every field except the element and data segment spaces. -/
structure SameCore (C D : context) : Prop where
  types : C.TYPES = D.TYPES
  funcs : C.FUNCS = D.FUNCS
  globals : C.GLOBALS = D.GLOBALS
  tables : C.TABLES = D.TABLES
  mems : C.MEMS = D.MEMS
  locals : C.LOCALS = D.LOCALS
  labels : C.LABELS = D.LABELS
  ret : C.RETURN = D.RETURN

/-- A context that agrees with `C` outside the segment spaces is `C` with those spaces replaced. -/
theorem SameCore.eq_segments {C D : context} (h : SameCore C D) :
    D = segments C D.ELEMS D.DATAS := by
  cases C
  cases D
  cases h
  simp_all [segments]

/-- A body typing moves to a context that agrees outside the segment spaces and has prefix-extended
segment spaces. -/
theorem instrs_transport_extend {C D : context} {ops : List instr} {ft : functype}
    (h : Instrs_ok C ops ft) (he : C.ELEMS.IsPrefix D.ELEMS)
    (hd : C.DATAS.IsPrefix D.DATAS) (hc : SameCore C D) : Instrs_ok D ops ft := by
  rw [hc.eq_segments]
  exact instrs_extend h _ _ he hd

end Itasca.Body.Context

end

/-! ## BodyContextComplete -/

section

/-!
# Body typing without data-index instructions

A body that contains no data-index instruction stays typed when its data space is replaced.
`typed_no_data` shows typing in an empty data space rules out data-index instructions, and
`instrs_transport_of_no_data` moves such a body between contexts that agree outside the segment
spaces and share their element space. This covers modules without a data count section.
-/

namespace Itasca.Binary

@[simp] theorem instructions_use_data_append (xs ys : List instr) :
    instructionsUseData (xs ++ ys) = (instructionsUseData xs || instructionsUseData ys) := by
  induction xs with
  | nil => rfl
  | cons op ops ih => simp [instructionsUseData, ih, Bool.or_assoc]

/-- Generated typing in a context with an empty data space implies no data-index instruction occurs,
even in nested or unreachable instructions. -/
theorem typed_no_data {C : context} {ops : List instr} {ft : functype}
    (h : Instrs_ok C ops ft) : C.DATAS = [] → instructionsUseData ops = false := by
  induction h using Instrs_ok.rec
    (motive_1 := fun C op _ _ => C.DATAS = [] → instructionUsesData op = false)
  all_goals first
    | rfl
    | (intro hd; simp_all [instructionsUseData, instructions_use_data_append])
    | (simp_all [instructionUsesData])

  case block => apply_assumption; assumption
  case loop => apply_assumption; assumption
  case «if» => constructor <;> (apply_assumption; assumption)

end Itasca.Binary

namespace Itasca.Body.Context

/-- A body without data-index instructions stays typed when the data space is replaced, and keeps
the same element space used by table operations. -/
theorem instrs_datas_of_syntax {C : context} {ops : List instr} {ft : functype}
    (h : Instrs_ok C ops ft) :
    ∀ datas, Binary.instructionsUseData ops = false →
      Instrs_ok (segments C C.ELEMS datas) ops ft := by
  induction h using Instrs_ok.rec
    (motive_1 := fun C op ft _ => ∀ datas, Binary.instructionUsesData op = false →
      Instr_ok (segments C C.ELEMS datas) op ft)
  case nop =>
    rename_i datas hs
    apply Instr_ok.nop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case unreachable =>
    rename_i datas hs
    apply Instr_ok.unreachable <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case drop =>
    rename_i datas hs
    apply Instr_ok.drop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case select_expl =>
    rename_i datas hs
    apply Instr_ok.select_expl <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case select_impl =>
    rename_i datas hs
    apply Instr_ok.select_impl <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case block =>
    rename_i datas hs
    simp only [Binary.instructionUsesData] at hs
    apply Instr_ok.block <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
      | exact blocktype_segments (by assumption) _ _
      | (apply_assumption; assumption)
  case loop =>
    rename_i datas hs
    simp only [Binary.instructionUsesData] at hs
    apply Instr_ok.loop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
      | exact blocktype_segments (by assumption) _ _
      | (apply_assumption; assumption)
  case «if» =>
    rename_i datas hs
    simp only [Binary.instructionUsesData, Bool.or_eq_false_iff] at hs
    obtain ⟨hyes, hno⟩ := hs
    apply Instr_ok.«if» <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
      | exact blocktype_segments (by assumption) _ _
      | (apply_assumption; assumption)
  case br =>
    rename_i datas hs
    apply Instr_ok.br <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case br_if =>
    rename_i datas hs
    apply Instr_ok.br_if <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case br_table =>
    rename_i datas hs
    apply Instr_ok.br_table <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case call =>
    rename_i datas hs
    apply Instr_ok.call <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case call_indirect =>
    rename_i datas hs
    apply Instr_ok.call_indirect <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case «return» =>
    rename_i datas hs
    apply Instr_ok.«return» <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case const =>
    rename_i datas hs
    apply Instr_ok.const <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case unop =>
    rename_i datas hs
    apply Instr_ok.unop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case binop =>
    rename_i datas hs
    apply Instr_ok.binop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case testop =>
    rename_i datas hs
    apply Instr_ok.testop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case relop =>
    rename_i datas hs
    apply Instr_ok.relop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case cvtop =>
    rename_i datas hs
    apply Instr_ok.cvtop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case ref_null =>
    rename_i datas hs
    apply Instr_ok.ref_null <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case ref_func =>
    rename_i datas hs
    apply Instr_ok.ref_func <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case ref_is_null =>
    rename_i datas hs
    apply Instr_ok.ref_is_null <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vconst =>
    rename_i datas hs
    apply Instr_ok.vconst <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vvunop =>
    rename_i datas hs
    apply Instr_ok.vvunop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vvbinop =>
    rename_i datas hs
    apply Instr_ok.vvbinop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vvternop =>
    rename_i datas hs
    apply Instr_ok.vvternop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vvtestop =>
    rename_i datas hs
    apply Instr_ok.vvtestop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vunop =>
    rename_i datas hs
    apply Instr_ok.vunop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vbinop =>
    rename_i datas hs
    apply Instr_ok.vbinop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vtestop =>
    rename_i datas hs
    apply Instr_ok.vtestop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vrelop =>
    rename_i datas hs
    apply Instr_ok.vrelop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vshiftop =>
    rename_i datas hs
    apply Instr_ok.vshiftop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vbitmask =>
    rename_i datas hs
    apply Instr_ok.vbitmask <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vswizzle =>
    rename_i datas hs
    apply Instr_ok.vswizzle <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vshuffle =>
    rename_i datas hs
    apply Instr_ok.vshuffle <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vsplat =>
    rename_i datas hs
    apply Instr_ok.vsplat <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vextract_lane =>
    rename_i datas hs
    apply Instr_ok.vextract_lane <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vreplace_lane =>
    rename_i datas hs
    apply Instr_ok.vreplace_lane <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vextunop =>
    rename_i datas hs
    apply Instr_ok.vextunop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vextbinop =>
    rename_i datas hs
    apply Instr_ok.vextbinop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vnarrow =>
    rename_i datas hs
    apply Instr_ok.vnarrow <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vcvtop =>
    rename_i datas hs
    apply Instr_ok.vcvtop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case local_get =>
    rename_i datas hs
    apply Instr_ok.local_get <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case local_set =>
    rename_i datas hs
    apply Instr_ok.local_set <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case local_tee =>
    rename_i datas hs
    apply Instr_ok.local_tee <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case global_get =>
    rename_i datas hs
    apply Instr_ok.global_get <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case global_set =>
    rename_i datas hs
    apply Instr_ok.global_set <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case table_get =>
    rename_i datas hs
    apply Instr_ok.table_get <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case table_set =>
    rename_i datas hs
    apply Instr_ok.table_set <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case table_size =>
    rename_i datas hs
    apply Instr_ok.table_size <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case table_grow =>
    rename_i datas hs
    apply Instr_ok.table_grow <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case table_fill =>
    rename_i datas hs
    apply Instr_ok.table_fill <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case table_copy =>
    rename_i datas hs
    apply Instr_ok.table_copy <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case table_init =>
    rename_i datas hs
    apply Instr_ok.table_init <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case elem_drop =>
    rename_i datas hs
    apply Instr_ok.elem_drop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case memory_size =>
    rename_i datas hs
    apply Instr_ok.memory_size <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case memory_grow =>
    rename_i datas hs
    apply Instr_ok.memory_grow <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case memory_fill =>
    rename_i datas hs
    apply Instr_ok.memory_fill <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case memory_copy =>
    rename_i datas hs
    apply Instr_ok.memory_copy <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case memory_init =>
    rename_i datas hs
    simp_all [Binary.instructionUsesData]
  case data_drop =>
    rename_i datas hs
    simp_all [Binary.instructionUsesData]
  case load_val =>
    rename_i datas hs
    apply Instr_ok.load_val <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case load_pack =>
    rename_i datas hs
    apply Instr_ok.load_pack <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case store_val =>
    rename_i datas hs
    apply Instr_ok.store_val <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case store_pack =>
    rename_i datas hs
    apply Instr_ok.store_pack <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vload_val =>
    rename_i datas hs
    apply Instr_ok.vload_val <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vload_pack =>
    rename_i datas hs
    apply Instr_ok.vload_pack <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vload_splat =>
    rename_i datas hs
    apply Instr_ok.vload_splat <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vload_zero =>
    rename_i datas hs
    apply Instr_ok.vload_zero <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vload_lane =>
    rename_i datas hs
    apply Instr_ok.vload_lane <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vstore =>
    rename_i datas hs
    apply Instr_ok.vstore <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case vstore_lane =>
    rename_i datas hs
    apply Instr_ok.vstore_lane <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
  case empty =>
    intros datas hs
    apply Instrs_ok.empty
    exact segments_wf (by assumption) _ _
  case instr =>
    intros datas hs
    simp only [Binary.instructionsUseData, Bool.or_false] at hs
    apply Instrs_ok.instr <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
      | exact blocktype_segments (by assumption) _ _
      | (apply_assumption; assumption)
  case seq =>
    intros datas hs
    simp only [Binary.instructions_use_data_append, Bool.or_eq_false_iff] at hs
    obtain ⟨hfirst, hrest⟩ := hs
    apply Instrs_ok.seq <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
      | exact blocktype_segments (by assumption) _ _
      | (apply_assumption; assumption)
  case sub =>
    intros datas hs
    apply Instrs_ok.sub <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
      | exact blocktype_segments (by assumption) _ _
      | (apply_assumption; assumption)
  case frame =>
    intros datas hs
    apply Instrs_ok.frame <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
      | exact blocktype_segments (by assumption) _ _
      | (apply_assumption; assumption)

/-- A body without data-index instructions moves to any context that agrees outside the segment
spaces and has the same element space. -/
theorem instrs_transport_of_no_data {C D : context} {ops : List instr} {ft : functype}
    (h : Instrs_ok C ops ft) (hs : Binary.instructionsUseData ops = false)
    (he : C.ELEMS = D.ELEMS) (hc : SameCore C D) : Instrs_ok D ops ft := by
  rw [hc.eq_segments, ← he]
  exact instrs_datas_of_syntax h _ hs

end Itasca.Body.Context

end

end

/-! ## Locals -/

section

/-!
# Entry contexts and local declarations

Function/segment contexts relate entry typing to generated function judgments. Local
building and decoding connect grouped declarations, expanded types and exact consumed byte
spans.
-/

/-! ## Context -/

section

/-!
# Code entry typing contexts

`ModuleContext` and `SegmentContext` describe the module-level typing context a code entry is
checked in. `bodyContext` is the context a function body is typed in, `Typed` is the declarative
certificate for one code entry, and `typed_func_ok` and `Typed.func_ok` turn it into the generated
`Func_ok` in the full module context.
-/

open Aeneas Aeneas.Std

namespace Itasca.CodeEntry

/-- The context `C` has the module's types, functions, globals, tables and memories translated from
`env`, with empty local and label spaces. -/
structure ModuleContext (env : metadata.Env) (C : context) : Prop where
  types : C.TYPES = env.types.val.map Translation.Environment.funcType
  funcs : C.FUNCS = env.func_types.val.map Translation.Environment.funcType
  globals : C.GLOBALS = env.global_types.val.map Translation.globalType
  tables : C.TABLES = env.table_types.val.map Translation.Environment.tableType
  mems : C.MEMS = env.mem_types.val.map Translation.Environment.memType
  locals : C.LOCALS = []
  labels : C.LABELS = []

/-- The final element and data spaces of `C` extend those available while validating a body. The
data count section supplies the body-visible data space. -/
structure SegmentContext (env : metadata.Env) (C : context) : Prop where
  elems : (Translation.Environment.elementTypes env).IsPrefix C.ELEMS
  datas : (Translation.Environment.dataTypes env).IsPrefix C.DATAS

/-- A typed body in an environment without a data count contains no data-index instruction,
regardless of control nesting or stack reachability. -/
theorem Typed.no_data {env typeIdx entry} (h : Typed env typeIdx entry)
    (hcount : env.data_count = none) : Binary.instructionsUseData entry.body = false :=
  Binary.typed_no_data h.typed (by simp [bodyContext, Translation.Environment.dataTypes, hcount])

/-- A module context is well formed. -/
theorem ModuleContext.wf {env C} (h : ModuleContext env C) : wf_context C := by
  have ht := h.tables
  have hm := h.mems
  cases C
  constructor
  · dsimp only at ht
    rw [ht]
    simp only [Forall, List.mem_map]
    rintro _ ⟨tt, _, rfl⟩
    exact Translation.Environment.table_type_wf tt
  · dsimp only at hm
    rw [hm]
    simp only [Forall, List.mem_map]
    rintro _ ⟨mt, _, rfl⟩
    exact Translation.Environment.mem_type_wf mt

/-- A body typed in `bodyContext` gives the generated function typing `Func_ok` in any full module
context `C` whose segment spaces extend those of the body. -/
theorem typed_func_ok {env : metadata.Env} {typeIdx : U32} {entry : Binary.Code}
    (hindex : typeIdx.val < env.types.val.length)
    (htyped : Instrs_ok (bodyContext env env.types.val[typeIdx.val].params.val
      entry.declared env.types.val[typeIdx.val].results.val) entry.body
      (instructionType env.types.val[typeIdx.val])) (C : context) (hc : ModuleContext env C)
    (hsegments : SegmentContext env C) :
    Func_ok C (function typeIdx entry) (Translation.Environment.funcType (env.types.val[typeIdx.val]'hindex)) := by
  let ft := env.types.val[typeIdx.val]'hindex
  let ps := ft.params.val.map Translation.valueType
  let ds := entry.declared.map Translation.valueType
  let rs := ft.results.val.map Translation.valueType
  let localC : context := ⟨[], [], [], [], [], [], [], ps ++ ds, [.mk_list rs], some (.mk_list rs)⟩
  have hlwf : wf_context localC := by constructor <;> simp [Forall]
  have hcore : Body.Context.SameCore
      (bodyContext env ft.params.val entry.declared ft.results.val) (localC ++ C) := by
    constructor
    · exact hc.types.symm
    · exact hc.funcs.symm
    · exact hc.globals.symm
    · exact hc.tables.symm
    · exact hc.mems.symm
    · change (ft.params.val ++ entry.declared).map Translation.valueType = (ps ++ ds) ++ C.LOCALS
      simp [hc.locals, ps, ds]
    · change [.mk_list rs] = [.mk_list rs] ++ C.LABELS
      simp [hc.labels]
    · rfl
  have ht := Body.Context.instrs_transport_extend (D := localC ++ C) htyped
    hsegments.elems hsegments.datas hcore
  have hw := (Spec.Completeness.well_formed htyped).2
  have he : Expr_ok (localC ++ C) entry.body (.mk_list rs) :=
    .mk_Expr_ok _ _ _ ht
      ((Spec.Completeness.well_formed ht).1) hw
  have hn : Forall (fun t => t ≠ valtype.BOT) ds := by
    simp only [ds, Forall, List.mem_map]
    rintro _ ⟨t, _, rfl⟩
    cases t <;> simp [Translation.valueType]
  have hi : typeIdx.val < C.TYPES.length := by simpa [hc.types] using hindex
  have hlookup : C.TYPES[typeIdx.val]! = Translation.Environment.funcType ft := by
    rw [hc.types, getElem!_pos _ _ (by simpa using hindex), List.getElem_map]
  have hf : wf_func (function typeIdx entry) :=
    .func_case_0 _ _ _ (Translation.Environment.index_wf typeIdx) hw
  simpa only [function, Translation.Environment.funcType, Map, List.map_map,
    Function.comp_def, ds, ps, rs, ft, localC] using
    Func_ok.mk_Func_ok C (.mk_uN typeIdx.val) ds entry.body ps rs hi hlookup hn he hc.wf (by simpa [function, Map, ds, List.map_map, Function.comp_def] using hf) hlwf

/-- A `Typed` certificate gives `Func_ok` in the full module context. -/
theorem Typed.func_ok {env : metadata.Env} {typeIdx : U32} {entry : Binary.Code}
     (h : Typed env typeIdx entry) (C : context) (hc : ModuleContext env C)
    (hsegments : SegmentContext env C) :
    Func_ok C (function typeIdx entry) (Translation.Environment.funcType (env.types.val[typeIdx.val]'h.type_lt)) :=
  typed_func_ok h.type_lt h.typed C hc hsegments

end Itasca.CodeEntry

end

/-! ## Locals -/

section

/-!
# Local declarations

Specifications of the extracted local-variable code used by `metadata.validate_code_entry_with`.
`metadata.decode_locals.spec` shows `metadata.decode_locals` decodes grouped local declarations into
`CodeEntry.Locals.declared` within `limits.MAX_LOCALS`, with the independent `LocalEncoding` byte
provenance. `metadata.build_func_locals.spec` shows the function's locals are the parameters
followed by the declared locals, and `metadata.push_locals.spec` is the replication helper.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- `metadata.build_func_locals` returns the parameters followed by the declared locals. The size
bound excludes the allocation overflow possible in a caller-built oversized environment. -/
@[step]
theorem metadata.build_func_locals.spec (params declared : Slice wasm_types.ValueType)
    (hsize : params.val.length + declared.val.length ≤ Usize.max) :
    metadata.build_func_locals params declared ⦃ locals =>
      locals.val = params.val ++ declared.val ⦄ := by
  obtain ⟨out, hout, heq⟩ := WP.spec_imp_exists (metadata.copy_value_types.spec params)
  rw [metadata.build_func_locals, hout]
  simp only [bind_ok]
  simpa [metadata.build_func_locals_loop, metadata.copy_value_types_loop,
    metadata.build_func_locals_loop.body, metadata.copy_value_types_loop.body,
    List.drop_zero, heq] using
    metadata.copy_value_types_loop.spec declared out 0#usize (by simp) (by simpa [heq] using hsize)

/-- The loop of `metadata.push_locals` appends the remaining `count - i` copies of `ty`. -/
@[step]
theorem metadata.push_locals_loop.spec (out : alloc.vec.Vec wasm_types.ValueType)
    (count : U32) (ty : wasm_types.ValueType) (i : U32)
    (hi : i.val ≤ count.val)
    (hsize : out.val.length + (count.val - i.val) ≤ Usize.max) :
    metadata.push_locals_loop out count ty i ⦃ result =>
      result.val = out.val ++ List.replicate (count.val - i.val) ty ⦄ := by
  unfold metadata.push_locals_loop
  apply loop.spec_decr_nat (fun p => count.val - p.2.val)
    (fun p => p.2.val ≤ count.val ∧
      p.1.val ++ List.replicate (count.val - p.2.val) ty =
        out.val ++ List.replicate (count.val - i.val) ty ∧
      p.1.val.length + (count.val - p.2.val) ≤ Usize.max)
  · rintro ⟨v, j⟩ ⟨hj, hv, hb⟩
    dsimp only at hj hv hb
    unfold metadata.push_locals_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : j.val = count.val := by scalar_tac
      simp [heq] at hv
      simp [hv]
    · rename_i hmore
      have hlt : j.val < count.val := by scalar_tac
      have hcapacity : v.val.length < Usize.max := by omega
      step
      step
      refine ⟨?_, ?_, ?_, ?_⟩
      all_goals try scalar_tac
      rw [out1_post, i1_post, ← hv]
      have hdiff : count.val - j.val = count.val - (j.val + 1) + 1 := by omega
      rw [hdiff, List.replicate_succ]
      simp [List.append_assoc]
  · exact ⟨hi, rfl, hsize⟩

/-- `metadata.push_locals` appends `count` copies of `ty`. -/
@[step]
theorem metadata.push_locals.spec (out : alloc.vec.Vec wasm_types.ValueType)
    (count : U32) (ty : wasm_types.ValueType)
    (hsize : out.val.length + count.val ≤ Usize.max) :
    metadata.push_locals out count ty ⦃ result =>
      result.val = out.val ++ List.replicate count.val ty ⦄ := by
  simpa [metadata.push_locals] using
    metadata.push_locals_loop.spec out count ty 0#u32 (by simp) (by simpa using hsize)

namespace CodeEntry.Locals

theorem at_snoc {data start pos next groups group}
    (hp : Binary.At (Binary.Rep Binary.LocalEncoding) data start groups pos)
    (hg : Binary.At Binary.LocalEncoding data pos group next) :
    Binary.At (Binary.Rep Binary.LocalEncoding) data start (groups ++ [group]) next := by
  obtain ⟨bs, hb, hs⟩ := hp
  obtain ⟨cs, hc, ht⟩ := hg
  exact ⟨bs ++ cs, hb.snoc hc, hs.append ht⟩

theorem local_at {data start pos next count ty}
    (hc : Binary.Leb128.Decoded data start count pos)
    (ht : Binary.At Binary.ValueTypeEncoding data pos ty next) :
    Binary.At Binary.LocalEncoding data start (count, ty) next := by
  obtain ⟨cs, hs, hl, hb, he⟩ := hc
  obtain ⟨ts, heTy, ht⟩ := ht
  obtain rfl := Binary.ValueTypeEncoding.reader_bytes.mp heTy
  exact ⟨cs ++ [Binary.valueByte ty], Binary.LocalEncoding.reader_parts.mpr ⟨cs, he, rfl⟩, (⟨hs, hl, hb⟩ : Body.Scalar.BytesAt data start cs pos).append ht⟩

end CodeEntry.Locals

/-- The loop of `metadata.decode_locals` decodes the remaining `groups - i` local groups, extends the
output by their expansion, and keeps it within `limits.MAX_LOCALS`. -/
@[step]
theorem metadata.decode_locals_loop.spec (data : Slice U8) (groups : U32)
    (out : alloc.vec.Vec wasm_types.ValueType) (q : Usize) (i : U32)
    (hi : i.val ≤ groups.val) (hq : q.val ≤ data.length)
    (hsize : out.val.length ≤ limits.MAX_LOCALS.val) :
    metadata.decode_locals_loop data groups out q i ⦃ r => match r with
      | .Ok (locals, next) => ∃ decoded,
          decoded.length = groups.val - i.val ∧
          Binary.At (Binary.Rep Binary.LocalEncoding) data q decoded next ∧
          locals.val = out.val ++ CodeEntry.Locals.declared decoded ∧
          locals.val.length ≤ limits.MAX_LOCALS.val
      | .Err _ => True ⦄ := by
  unfold metadata.decode_locals_loop
  apply loop.spec_decr_nat (fun s => groups.val - s.2.2.val)
    (fun s => i.val ≤ s.2.2.val ∧ s.2.2.val ≤ groups.val ∧
      ∃ decoded, decoded.length = s.2.2.val - i.val ∧
        Binary.At (Binary.Rep Binary.LocalEncoding) data q decoded s.2.1 ∧
        s.1.val = out.val ++ CodeEntry.Locals.declared decoded ∧
        s.1.val.length ≤ limits.MAX_LOCALS.val)
  · rintro ⟨v, p, j⟩ ⟨hij, hj, decoded, hlen, hbytes, hvals, hcap⟩
    dsimp only at hij hj hlen hbytes hvals hcap
    unfold metadata.decode_locals_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : j.val = groups.val := by scalar_tac
      simp only [WP.spec_ok]
      exact ⟨decoded, by omega, hbytes, hvals, hcap⟩
    · rename_i hmore
      have hlt : j.val < groups.val := by scalar_tac
      obtain ⟨r, hr, hrpost⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data p)
      rw [hr]
      cases r with
      | Err e =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            error.Error.Insts.CoreConvertFromOpError.from]
      | Ok pair =>
          obtain ⟨count, p1⟩ := pair
          obtain ⟨r, ht, htpost⟩ := WP.spec_imp_exists (metadata.decode_value_type.spec data p1)
          simp [core.result.Result.Insts.CoreOpsTry.branch]
          rw [ht]
          cases r with
          | Err e =>
              simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok pair =>
              obtain ⟨ty, p2⟩ := pair
              have hlocal := CodeEntry.Locals.local_at hrpost htpost
              simp only [bind_ok]
              step
              step
              split
              · simp
              · rename_i hroom
                have hcapacity : v.val.length + count.val ≤ Usize.max := by
                  have : limits.MAX_LOCALS.val < Usize.max := by
                    simp only [limits.MAX_LOCALS]
                    scalar_tac
                  scalar_tac
                step
                step
                refine ⟨?_, ?_, ⟨decoded ++ [(count, ty)], ?_, ?_, ?_, ?_⟩, ?_⟩
                · scalar_tac
                · scalar_tac
                · simp only [List.length_append, List.length_singleton]
                  scalar_tac
                · exact CodeEntry.Locals.at_snoc hbytes hlocal
                · rw [out1_post, hvals]
                  simp [CodeEntry.Locals.declared, List.flatMap_append, List.append_assoc]
                · simp only [out1_post, List.length_append, List.length_replicate]
                  scalar_tac
                · scalar_tac
  · refine ⟨le_refl _, hi, [], by simp, ?_, by simp [CodeEntry.Locals.declared], hsize⟩
    exact ⟨[], .nil, Body.Scalar.BytesAt.nil data q hq⟩

/-- `metadata.decode_locals` terminates, and on success returns the expansion of independently
encoded local groups within `limits.MAX_LOCALS`. -/
@[step]
theorem metadata.decode_locals.spec (data : Slice U8) (pos : Usize) :
    metadata.decode_locals data pos ⦃ r => match r with
      | .Ok (locals, next) => ∃ groups,
          Binary.At (Binary.VecEncoding Binary.LocalEncoding) data pos groups next ∧
          locals.val = CodeEntry.Locals.declared groups ∧
          locals.val.length ≤ limits.MAX_LOCALS.val
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e =>
      simp [metadata.decode_locals, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
      obtain ⟨groups, start⟩ := pair
      have hs := hp.span
      rw [metadata.decode_locals, hr]
      simp [core.result.Result.Insts.CoreOpsTry.branch]
      apply WP.spec_mono (metadata.decode_locals_loop.spec data groups (alloc.vec.Vec.new _) start 0#u32
        (by simp) hs.2.2 (by simp))
      rintro r h
      cases r with
      | Err e => trivial
      | Ok pair =>
          obtain ⟨locals, next⟩ := pair
          obtain ⟨decoded, hn, hb, hv, hc⟩ := h
          refine ⟨decoded, ?_, by simpa [alloc.vec.Vec.new] using hv, hc⟩
          obtain ⟨count, hstart, hlength, hbound, he⟩ := hp
          obtain ⟨bytes, he', hs'⟩ := hb
          refine ⟨count ++ bytes, ⟨count, bytes, ?_, he', rfl⟩, ?_⟩
          · simpa using (hn ▸ he)
          · exact (⟨hstart, hlength, hbound⟩ : Body.Scalar.BytesAt data pos count start).append hs'

end Itasca

end

/-! ## Encoding -/

section

/-!
# Code entry encodings from byte provenance

Conversions between the streaming byte provenance used by the extracted code-entry reader
(`Body.Scalar.Consumed`, `Body.Scalar.BytesAt`) and the independent module grammar
(`At`, `Rep`), and `slice_bytes` for the body slice a parser returns.
-/

open Aeneas Aeneas.Std

namespace Itasca.Binary

/-- The streaming token provenance of a body is an `At (Rep Body.Scalar.TokenEncoding)` of the module
grammar. -/
theorem consumed_rep {data start tokens next}
    (h : Body.Scalar.Consumed data start tokens next) :
    At (Rep Body.Scalar.TokenEncoding) data start tokens next := by
  induction h with
  | nil hb => exact ⟨[], .nil, Body.Scalar.BytesAt.nil _ _ hb⟩
  | snoc hprev ht ih =>
    obtain ⟨bs, he, hs⟩ := ih
    obtain ⟨cs, hc, hp⟩ := ht
    exact ⟨bs ++ cs, he.snoc hc, hs.append hp⟩

/-- A slice taken from `first` to `last` holds exactly the parent buffer's bytes in that
interval. -/
theorem slice_bytes {data : Slice U8} {first last : Usize} {body : Slice U8}
    (hfirst : first.val ≤ last.val) (hlast : last.val ≤ data.length)
    (hbody : body.val = data.val.slice first.val last.val) :
    Body.Scalar.BytesAt data first body.val last := by
  refine ⟨?_, ?_, hlast⟩
  · rw [hbody, List.slice]
    have he : first.val + (last.val - first.val) = last.val := by omega
    simpa only [List.drop_drop, he] using
      (List.take_append_drop (last.val - first.val) (data.val.drop first.val)).symm
  · rw [hbody, List.slice_length]
    simp only [Slice.length] at hlast
    omega

/-- A token repetition with matching bytes gives streaming provenance. -/
theorem rep_consumed {data start next tokens bytes}
    (he : Rep Body.Scalar.TokenEncoding tokens bytes) (hs : Body.Scalar.BytesAt data start bytes next) :
    Body.Scalar.Consumed data start tokens next := by
  induction he generalizing start with
  | nil =>
    have hn := hs.empty
    subst next
    exact .nil _ hs.bound
  | cons ht hrest ih =>
    obtain ⟨middle, hfirst, hrest⟩ := hs.split
    exact Body.Scalar.Consumed.cons_iff.mpr ⟨middle, ⟨_, ht, hfirst⟩, ih hrest⟩

end Itasca.Binary

end

end
