import Itasca.Module.Code.BodyContext
import Itasca.Module.Code.DataUse

namespace Itasca.BodyContext

/-- Syntax without data-index operations permits data contexts to be replaced,
while retaining the complete element space used by table operations. -/
theorem instrs_datas_of_syntax {C : context} {ops : List instr} {ft : functype}
    (h : Instrs_ok C ops ft) :
    ∀ datas, ModuleBinary.instructionsUseData ops = false →
      Instrs_ok (segments C C.ELEMS datas) ops ft := by
  induction h using Instrs_ok.rec
    (motive_1 := fun C op ft _ => ∀ datas, ModuleBinary.instructionUsesData op = false →
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
    simp only [ModuleBinary.instructionUsesData] at hs
    apply Instr_ok.block <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
      | exact blocktype_segments (by assumption) _ _
      | (apply_assumption; assumption)
  case loop =>
    rename_i datas hs
    simp only [ModuleBinary.instructionUsesData] at hs
    apply Instr_ok.loop <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
      | exact blocktype_segments (by assumption) _ _
      | (apply_assumption; assumption)
  case «if» =>
    rename_i datas hs
    simp only [ModuleBinary.instructionUsesData, Bool.or_eq_false_iff] at hs
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
    simp_all [ModuleBinary.instructionUsesData]
  case data_drop =>
    rename_i datas hs
    simp_all [ModuleBinary.instructionUsesData]
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
    simp only [ModuleBinary.instructionsUseData, Bool.or_false] at hs
    apply Instrs_ok.instr <;> first
      | assumption
      | exact segments_wf (by assumption) _ _
      | exact blocktype_segments (by assumption) _ _
      | (apply_assumption; assumption)
  case seq =>
    intros datas hs
    simp only [ModuleBinary.instructionsUseData_append, Bool.or_eq_false_iff] at hs
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

theorem instrs_transport_of_no_data {C D : context} {ops : List instr} {ft : functype}
    (h : Instrs_ok C ops ft) (hs : ModuleBinary.instructionsUseData ops = false)
    (he : C.ELEMS = D.ELEMS) (hc : SameCore C D) : Instrs_ok D ops ft := by
  rw [hc.eq_segments, ← he]
  exact instrs_datas_of_syntax h _ hs

end Itasca.BodyContext
