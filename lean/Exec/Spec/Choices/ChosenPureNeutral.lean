import Exec.Spec.Choices.VectorPureForced
namespace Exec.Spec

/-- The active pure redex may be ordinary or a deterministic integer SIMD
operator. Scalar numeric operators and vector conversions are handled by their
separate primitive adapters. -/
def neutralPureRedex : List admininstr → Bool
  | [.CONST _ _,.UNOP _ _] | [.CONST _ _,.CONST _ _,.BINOP _ _]
  | [.CONST _ _,.CVTOP _ _ _] | [.VCONST _ _,.VCVTOP _ _ _] => false
  | [.VCONST _ _,.VUNOP _ op] => !vectorUnaryFloat op
  | [.VCONST _ _,.VCONST _ _,.VBINOP _ op] => !vectorBinaryFloat op
  | _ => true

set_option maxHeartbeats 2000000 in
theorem chosen_pure_neutral (occurrence : Nat) {choices : SourceChoices}
    (vector : choices.vector=firstVectorChoice) {before after : List admininstr}
    (source : Step_pure before after) (neutral : neutralPureRedex before=true) :
    ChosenPure choices occurrence before after := by
  have original := source
  cases source
  all_goals try {
    apply ChosenPure.ordinary original
    try casesm* val
    try casesm* ref
    all_goals rfl
  }
  all_goals try { simp [neutralPureRedex] at neutral }
  all_goals try { exact .ordinary original (label_redex_choice_free _ _ _) }
  all_goals try { exact .ordinary original (frame_redex_choice_free _ _ _) }
  case trap_vals front tail nonempty frontWf tailWf trapWf =>
    apply ChosenPure.ordinary original
    simpa only [SpecExt.vals,Map,List.append_assoc] using trap_redex_choice_free front tail
  all_goals simp only [neutralPureRedex,Bool.not_eq_true'] at neutral
  all_goals first
    | (have selected := chosen_vector_nonfloat_pure occurrence original (.unary _ _ _) (some _) rfl rfl neutral
       rw [←vector] at selected
       exact .vector selected)
    | (have selected := chosen_vector_nonfloat_pure occurrence original (.binary _ _ _ _) (some _) rfl rfl neutral
       rw [←vector] at selected
       exact .vector selected)
    | (have selected := chosen_vector_nonfloat_pure occurrence original (.unary _ _ _) none rfl rfl neutral
       rw [←vector] at selected
       exact .vector selected)
    | (have selected := chosen_vector_nonfloat_pure occurrence original (.binary _ _ _ _) none rfl rfl neutral
       rw [←vector] at selected
       exact .vector selected)
end Exec.Spec
