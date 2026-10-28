import Exec.Abs.ModuleBindingsExtension

namespace Itasca.Runtime.Abs
open SpecExt Itasca.Runtime.Spec

/-- Store extension preserves the type of every existing operand/reference. -/
theorem val_typed_extend {before after : store} (extension : Extend_store before after)
    {value : val} {ty : valtype} (typed : Val_ok before value ty) : Val_ok after value ty := by
  have fresh := (extend_store_wf extension).2
  cases typed with
  | numtype ty bits _ wf => exact .numtype after ty bits fresh wf
  | vectype ty bits _ wf => exact .vectype after ty bits fresh wf
  | reftype value ty reference _ => exact .reftype after value ty (ref_ok_extend extension reference) fresh

theorem results_typed_extend {before after : store} (extension : Extend_store before after)
    {types : List valtype} {values : List val} (typed : ResultsTyped before types values) :
    ResultsTyped after types values := typed.imp (fun _ _ value => val_typed_extend extension value)

theorem FrameTyped.extend {before after : store} (extension : Extend_store before after)
    {frame incoming} (typed : FrameTyped before frame incoming) : FrameTyped after frame incoming := by
  cases typed with
  | mk context bindings locals localTypes values result code wf =>
    exact .mk context (bindings.extend extension) locals (results_typed_extend extension localTypes)
      (results_typed_extend extension values) result code wf

theorem FramesTyped.extend {before after : store} (extension : Extend_store before after)
    {frames incoming} (typed : FramesTyped before frames incoming) : FramesTyped after frames incoming := by
  induction typed with
  | nil results => exact .nil results
  | cons frame rest ih => exact .cons (frame.extend extension) ih

/-- Content updates preserve the complete abstract typing invariant. Adding
functions requires a separate typing attachment for those new bodies. -/
theorem ATyped.extend_same {state : AState} {after : _root_.store}
    (typed : ATyped state) (extension : Extend_store state.store after)
    (functions : after.FUNCS = state.store.FUNCS) : ATyped {state with store := after} :=
  ⟨(extend_store_wf extension).2, typed.functions.extend_same extension functions,
    typed.ambient, typed.frames.extend extension, typed.results, typed.activeResults, typed.heights⟩
end Itasca.Runtime.Abs
