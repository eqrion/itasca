import Exec.Spec.Choices.TrapNormalization
import Exec.Spec.Choices.NumericPredicateDeterminism
import Exec.Spec.Choices.VectorDeterminism
import Exec.Spec.Choices.SimdAuxDeterminism
import Exec.Spec.Choices.SimdListDeterminism
import Exec.Spec.Choices.ValuePrefixSyntax
import Exec.Spec.Choices.ControlSyntaxUniqueness
import Exec.Spec.Choices.NumericInputUniqueness
import Exec.Spec.Choices.SimdExtendedDeterminism
import Exec.Spec.Choices.SimdRearrangeUniqueness
/-! Pure source reductions are functional when they do not consume an explicit
choice and are outside active trap cleanup. Trap cleanup has its independent
strong normalization theorem rather than one-step determinism. -/
namespace Exec.Spec
open SpecExt
private def lastPureInstruction (body : List admininstr) : Option Nat := body.getLast? |>.map admininstr.ctorIdx

inductive PureTrapRedex : List admininstr → Prop
  | instructions (front : List val) (tail : List admininstr) : PureTrapRedex (vals front++([.TRAP]++tail))
  | label (arity : Nat) (cont : List instr) : PureTrapRedex [.LABEL_ arity cont [.TRAP]]
  | frame (arity : Nat) (frame : _root_.frame) : PureTrapRedex [.FRAME_ arity frame [.TRAP]]

set_option maxHeartbeats 1000000 in
theorem choice_free_pure_deterministic {before other left right : List admininstr}
    (first : Step_pure before left) (second : Step_pure other right) (same : before=other)
    (free : ChoiceFreePureRedex before) (regular : ¬ PureTrapRedex before) : left=right := by
  have otherRegular : ¬ PureTrapRedex other := by rw [← same]; exact regular
  have last := congrArg lastPureInstruction same
  cases first
  all_goals try { simp [ChoiceFreePureRedex,pureRedexUsesChoice] at free }
  case trap_vals => exact False.elim (regular (.instructions _ _))
  case trap_label => exact False.elim (regular (.label _ _))
  case trap_frame => exact False.elim (regular (.frame _ _))
  all_goals cases second
  repeat' (case trap_vals => exact False.elim (otherRegular (.instructions _ _)))
  repeat' (case trap_label => exact False.elim (otherRegular (.label _ _)))
  repeat' (case trap_frame => exact False.elim (otherRegular (.frame _ _)))
  all_goals cases last
  all_goals try injections
  all_goals subst_vars
  all_goals try injections
  all_goals subst_vars
  all_goals try injections
  all_goals subst_vars
  all_goals try injections
  all_goals subst_vars
  all_goals try (with_reducible rfl)
  all_goals try (with_reducible contradiction)
  all_goals try clear free
  all_goals try clear regular
  all_goals try clear otherRegular
  all_goals try have kindEq := source_lane_kind_injective (by assumption)
  all_goals subst_vars
  all_goals try have kindEq := source_lane_kind_injective (by assumption)
  all_goals subst_vars
  all_goals try have kindEq := source_pack_lane_kind_injective (by assumption)
  all_goals subst_vars
  all_goals try have kindEq := source_num_lane_kind_injective (by assumption)
  all_goals subst_vars
  all_goals try (with_reducible rfl)
  all_goals try simp only [Map,← List.map_append] at *
  all_goals try simp only [List.append_assoc] at *
  case label_vals.br_zero | label_vals.br_succ =>
    exact False.elim (values_ne_nonvalue_prefix _ _ (.BR _) _ rfl (by assumption))
  case br_zero.label_vals | br_succ.label_vals =>
    exact False.elim (values_ne_nonvalue_prefix _ _ (.BR _) _ rfl (Eq.symm (by assumption)))
  case label_vals.return_label | frame_vals.return_frame =>
    exact False.elim (values_ne_nonvalue_prefix _ _ .RETURN _ rfl (by assumption))
  case return_label.label_vals | return_frame.frame_vals =>
    exact False.elim (values_ne_nonvalue_prefix _ _ .RETURN _ rfl (Eq.symm (by assumption)))
  case br_zero.return_label | br_succ.return_label =>
    exact False.elim (branch_return_prefix_disjoint (by assumption))
  case return_label.br_zero | return_label.br_succ =>
    exact False.elim (branch_return_prefix_disjoint (Eq.symm (by assumption)))
  case br_zero.br_succ => exact False.elim (branch_zero_successor_prefix_disjoint (by assumption))
  case br_succ.br_zero => exact False.elim (branch_zero_successor_prefix_disjoint (Eq.symm (by assumption)))
  case br_zero.br_zero =>
    congr 2
    apply retained_value_suffix_unique (by assumption) rfl rfl
    omega
  case return_frame.return_frame =>
    apply congrArg vals
    apply retained_value_suffix_unique (by assumption) rfl rfl
    omega
  case return_label.return_label =>
    congr 2
    exact ordinary_value_prefix_unique (by assumption) rfl rfl
  case br_succ.br_succ => exact source_branch_successor_unique (by assumption)
  case testop.testop | relop.relop =>
    casesm* Option num_
    all_goals try (with_reducible contradiction)
    all_goals apply congrArg (fun value => [admininstr.CONST .I32 value])
    all_goals first
      | exact numeric_testop_results_unique (by assumption) (by assumption)
      | exact numeric_relop_results_unique (by assumption) (by assumption)
  case vvtestop.vvtestop =>
    apply congrArg (fun value => [admininstr.CONST .I32 value])
    apply source_integer_num_unique .I32
    all_goals first | assumption | (with_reducible grind only [ine_results_unique])
  case ref_is_null_true.ref_is_null_false | ref_is_null_false.ref_is_null_true =>
    casesm* ref
    all_goals simp only [admininstr_ref] at *
    all_goals try injections
    all_goals subst_vars
    all_goals exfalso
    all_goals rename_i rt negative
    all_goals apply negative
    all_goals exact .ref_is_null_true_0 (.REF_NULL rt) rt rfl (by assumption) (by assumption)
  case vtestop_true.vtestop_false | vtestop_false.vtestop_true =>
    exfalso
    apply (by assumption : ¬ Step_pure_before_vtestop_false _)
    exact .vtestop_true_0 _ _ _ _ rfl (by assumption) (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption) (by assumption)

  case select_true.select_true | select_false.select_false | local_tee.local_tee => grind
  case br_table_lt.br_table_ge | br_table_ge.br_table_lt => omega
  case vrelop.vrelop | vextunop.vextunop | vextbinop.vextbinop =>
    casesm* Option vec_
    all_goals try (with_reducible contradiction)
    all_goals apply congrArg (fun value => [admininstr.VCONST .V128 value])
    all_goals first
      | exact vector_relop_some_unique (by assumption) (by assumption)
      | exact vector_extunop_some_unique (by assumption) (by assumption)
      | exact vector_extbinop_some_unique (by assumption) (by assumption)
  case vshiftop.vshiftop =>
    congr 4
    apply vector_shift_list_unique _ _ _
    rotate_left 2
    all_goals assumption
  case vbitmask.vbitmask =>
    apply bitmask_values_unique _ _ (by assumption) (by assumption) (by assumption) (by assumption)
    all_goals assumption
  case vshuffle.vshuffle =>
    apply shuffle_values_unique _ _ _ (by assumption) (by assumption)
  case vsplat.vsplat =>
    congr 4
    apply congrArg Option.get!
    exact packnum_present_unique (by assumption) (by assumption) (by assumption) (by assumption)
  case vreplace_lane.vreplace_lane =>
    congr 4
    funext value
    apply congrArg Option.get!
    exact packnum_present_unique (by assumption) (by assumption) (by assumption) (by assumption)
  case vextract_lane_num.vextract_lane_num =>
    apply congrArg (fun reply : Option num_ => [admininstr.CONST _ reply.get!])
    exact unpacknum_present_unique (by assumption) (by assumption) (by assumption) (by assumption)
  case vextract_lane_pack.vextract_lane_pack =>
    apply congrArg (fun value => [admininstr.CONST .I32 value])
    apply source_integer_num_unique .I32
    all_goals first | assumption | (with_reducible grind only [])
  case vnarrow.vnarrow =>
    have inj : Function.Injective lanetype_Jnn := fun _ _ h => source_lane_kind_injective h
    simp only [inj.eq_iff] at *
    subst_vars
    with_reducible rfl

theorem PureTrapRedex.active {code : List admininstr} (trap : PureTrapRedex code) : activeTrap code=true := by
  cases trap <;> simp only [activeTrap_vals,activeTrap,List.cons_append,List.nil_append]

theorem choice_free_pure_nonactive_deterministic {before left right : List admininstr}
    (first : Step_pure before left) (second : Step_pure before right)
    (free : ChoiceFreePureRedex before) (nonactive : activeTrap before=false) : left=right := by
  apply choice_free_pure_deterministic first second rfl free
  intro trap
  have active := trap.active
  rw [nonactive] at active
  contradiction
end Exec.Spec
