import Itasca.Runtime.SourceMachine.Progress
import Itasca.Runtime.SourceMachine.Sim.Context

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

/-- The semantic label invariant provides syntax well-formedness for every
continuation used while lifting source reductions through nested labels. -/
theorem code_stack_labels_wf {C : context} {labels : List Label}
    {stack results : List valtype} {code : List instr}
    (h : CodeStackTyped C labels stack code results) : LabelsWf labels := by
  induction h with
  | outer _ => exact forall_nil _
  | @label label labels saved operands code results height nesting body cont after ih =>
    intro l hl
    simp only [List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact ⟨(Itasca.DeclarativeComplete.wellFormed cont).2, code_stack_wf after⟩
    · exact ih l hl

theorem frame_typed_wf {s : store} {f : AFrame} {incoming : List valtype}
    (h : FrameTyped s f incoming) : FrameWf f := by
  cases h with
  | mk C bindings localTypes locals values returns code hw =>
    exact ⟨hw, code_stack_labels_wf code, results_typed_wf values, code_stack_wf code⟩

theorem frames_typed_wf {s : store} {frames : List AFrame} {incoming : List valtype}
    (h : FramesTyped s frames incoming) : Forall FrameWf frames := by
  induction h with
  | nil => exact forall_nil _
  | cons hf _ ih =>
    intro f hm
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact frame_typed_wf hf
    · exact ih f hm

theorem decode_labels_wf (labels : List Label) (values : List val) (code : List admininstr)
    (hl : LabelsWf labels) (hv : Forall wf_val values) (hc : Forall wf_admininstr code) :
    Forall wf_admininstr (decodeLabels labels values code) := by
  induction labels generalizing values code with
  | nil => exact forall_append (wf_vals hv) hc
  | cons label labels ih =>
    have hlabel := hl label (by simp)
    apply ih _ _ (fun l hm => hl l (by simp [hm]))
      (fun value hm => hv value (List.mem_of_mem_take hm))
    apply forall_append ?_ (wf_instrs hlabel.2)
    intro i hi
    simp only [List.mem_singleton] at hi
    subst i
    exact .admininstr_case_71 _ _ _ hlabel.1
      (forall_append (wf_vals (fun value hm => hv value (List.mem_of_mem_drop hm))) hc)

theorem decode_frames_wf (frames : List AFrame) (code : List admininstr)
    (hf : Forall FrameWf frames) (hc : Forall wf_admininstr code) :
    Forall wf_admininstr (decodeFrames frames code) := by
  induction frames generalizing code with
  | nil => exact hc
  | cons f rest ih =>
    obtain ⟨frame, labels, values, body⟩ := hf f (by simp)
    apply ih _ (fun f hm => hf f (by simp [hm]))
    intro i hi
    simp only [List.mem_singleton] at hi
    subst i
    exact .admininstr_case_72 _ _ _ frame
      (decode_labels_wf f.labels f.vals _ labels values (forall_append hc (wf_instrs body)))

/-- Source typing supplies all endpoint well-formedness premises needed by the
generated reduction rules and by zero-step administrative simulations. -/
theorem ATyped.decode_wf {s : AState} (h : ATyped s) : wf_config (decode s) :=
  wf_config_make h.store h.ambient
    (decode_frames_wf s.frames (vals s.results) (frames_typed_wf h.frames) (wf_vals h.results))

end Itasca.Runtime.SourceMachine
