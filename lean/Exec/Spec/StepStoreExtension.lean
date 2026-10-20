import Exec.Spec.Typing.HostStepPreservation
namespace Exec.Spec
open SpecExt

/-- Semantic source typing exposes the store extension carried by every
ordinary or completed host transition, including committed error effects. -/
theorem stepH_store_extension {s t : store} {f g : frame} {before after : List admininstr}
    {events : List HostEvent} {expected : resulttype}
    (step : StepH ⟨⟨s,f⟩,before⟩ events ⟨⟨t,g⟩,after⟩)
    (typed : Config_ok ⟨⟨s,f⟩,before⟩ expected) : Extend_store s t := by
  cases typed with
  | mk_Config_ok _ _ _ output context oldState expression contextWf _ _ =>
    have frameTyped : Frame_ok s f context := by cases oldState; assumption
    have storeTyped : Store_ok s := by cases oldState; assumption
    have body : Instrs_ok2 s context before (.mk_functype (.mk_list []) (.mk_list output)) := by
      cases expression
      assumption
    exact (stepH_typing_replacement step context [] output storeTyped (.of_frame_ok frameTyped) body).1
end Exec.Spec
