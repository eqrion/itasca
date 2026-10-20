import Exec.Spec.Choices.CoreChoiceStep
namespace Exec.Spec
open SpecExt

private theorem no_memory_growth (free : ChoiceFreeInstruction .MEMORY_GROW) : False := by
  cases free
  simp [ordinaryChoiceTag] at *

private theorem no_table_growth {index : idx} (free : ChoiceFreeInstruction (.TABLE_GROW index)) : False := by
  cases free
  simp [ordinaryChoiceTag] at *

set_option maxHeartbeats 2000000 in
theorem Step.contextualCore {choices : SourceChoices} {occurrence : Nat} {before after : config}
    (source : Step before after) : ChoiceFreeConfig before → ContextualCore choices occurrence before [] after := by
  induction source
  all_goals intro free
  case pure z body result source input output =>
    exact (CoreChoiceStep.ordinary_pure source free.pure input output).contextual
  case read z body result source input output =>
    exact (CoreChoiceStep.ordinary_read source input output).contextual
  case ctxt_label z arity continuation body z' result source input output inside outside ih =>
    have nested := (free (.LABEL_ arity continuation body) (by simp [ChoiceFreeConfig])).label_body
    exact (CoreChoiceStep.label (.ordinary source nested) input output).contextual
  case ctxt_frame s ambient arity inner body s' inner' result source input output inside outside ih =>
    have nested := (free (.FRAME_ arity inner body) (by simp [ChoiceFreeConfig])).frame_body
    exact (CoreChoiceStep.frame (.ordinary source nested) input output).contextual
  case ctxt_instrs z front body tail z' result source nonempty input output inside outside ih =>
    exact (ih free.instructions).instrs front tail
  case memory_grow_succeed | memory_grow_fail =>
    exact False.elim (no_memory_growth (free .MEMORY_GROW (by simp [ChoiceFreeConfig])))
  case table_grow_succeed | table_grow_fail =>
    exact False.elim (no_table_growth (free _ (by
      simp only [List.mem_cons]
      exact Or.inr (Or.inr (Or.inl rfl)))))
  all_goals apply CoreChoiceStep.contextual
  all_goals apply CoreChoiceStep.write
  all_goals solve_by_elim (maxDepth := 16) [DirectWrite.local_set,DirectWrite.global_set,
    DirectWrite.table_set_trap,DirectWrite.table_set_val,DirectWrite.elem_drop,
    DirectWrite.store_num_trap,DirectWrite.store_num_val,DirectWrite.store_pack_trap,DirectWrite.store_pack_val,
    DirectWrite.vstore_oob,DirectWrite.vstore_val,DirectWrite.vstore_lane_oob,DirectWrite.vstore_lane_val,DirectWrite.data_drop]

set_option maxHeartbeats 2000000 in
theorem ChoiceStep.contextualCore {choices : SourceChoices} {occurrence : Nat} {before after : config}
    {events : List HostEvent} (source : ChoiceStep choices occurrence before events after) :
    ContextualCore choices occurrence before events after := by
  induction source
  case ordinary source free => exact Exec.Spec.Step.contextualCore source free
  case ordinary_pure source free input output =>
    exact (CoreChoiceStep.ordinary_pure source free input output).contextual
  case ordinary_read source input output =>
    exact (CoreChoiceStep.ordinary_read source input output).contextual
  case ordinary_write source free => exact Exec.Spec.Step.contextualCore source free.config
  case instrs source nonempty input output ih => exact ih.instrs _ _
  all_goals apply CoreChoiceStep.contextual
  all_goals solve_by_elim (maxDepth := 16) [CoreChoiceStep.numeric,CoreChoiceStep.vector,
    CoreChoiceStep.memory,CoreChoiceStep.table,CoreChoiceStep.host,CoreChoiceStep.label,CoreChoiceStep.frame]
end Exec.Spec
