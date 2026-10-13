import Itasca.Spec.TypingInversion
import Itasca.Wasm1.Profile

/-!
# Body typing under extended segment spaces

A body typed in a context with short element and data spaces stays typed when those spaces are
extended. `instrs_extend` shows `Instrs_ok` is preserved by prefix extension of the segment spaces,
and `instrs_transport` and `expr_transport` move a body typing between contexts that agree on every
other field. These results apply to the generated typing rules, so they hold for both profiles.
-/

open Aeneas Aeneas.Std

namespace Itasca.BodyContext

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

/-- Empty segment spaces are a special case of index-preserving extension. -/
theorem instrs_segments {C : context} {ops : List instr} {ft : functype}
    (h : Instrs_ok C ops ft) (elems : List elemtype) (datas : List datatype)
    (he : C.ELEMS = []) (hd : C.DATAS = []) :
    Instrs_ok (segments C elems datas) ops ft :=
  instrs_extend h elems datas (by simp [he]) (by simp [hd])

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

/-- A body typing in a context with empty segment spaces moves to any context that agrees outside
the segment spaces. -/
theorem instrs_transport {C D : context} {ops : List instr} {ft : functype}
    (h : Instrs_ok C ops ft) (he : C.ELEMS = []) (hd : C.DATAS = [])
    (hc : SameCore C D) : Instrs_ok D ops ft := by
  rw [hc.eq_segments]
  exact instrs_segments h _ _ he hd

/-- `instrs_transport` for typed expressions. -/
theorem expr_transport {C D : context} {ops : expr} {rt : resulttype}
    (h : Expr_ok C ops rt) (he : C.ELEMS = []) (hd : C.DATAS = [])
    (hc : SameCore C D) : Expr_ok D ops rt := by
  cases h with
  | mk_Expr_ok ts ht hw hops =>
    exact .mk_Expr_ok D ops ts (instrs_transport ht he hd hc)
      (by rw [hc.eq_segments]; exact segments_wf hw _ _) hops

end Itasca.BodyContext
