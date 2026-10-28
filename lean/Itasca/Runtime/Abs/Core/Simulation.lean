import Itasca.Runtime.Abs.Sim.Basic
import Itasca.Runtime.Spec.Globals

namespace Itasca.Runtime.Abs
open SpecExt Itasca.Runtime.Spec

/-- Lift a store-changing redex through the active operand stack, labels and
suspended callers. The same frame syntax is interpreted in the new store. -/
theorem mutable_stack_simulation (before afterStore : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (instruction : instr) (after : List instr)
    (baseValues consumed produced : List val)
    (ha : wf_frame ambient)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (step : StepH ⟨⟨before, f.toFrame⟩, vals consumed ++ [admininstr_instr instruction]⟩ []
      ⟨⟨afterStore, f.toFrame⟩, vals produced⟩) :
    StepH (decode ⟨before, ambient,
      { f with code := instruction :: after, vals := baseValues ++ consumed } :: rest, []⟩) []
      (decode ⟨afterStore, ambient,
      { f with code := after, vals := baseValues ++ produced } :: rest, []⟩) := by
  have h₁ := stepH_instrs step [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc)
  have h₂ := stepH_decodeLabels h₁ f.labels baseValues hl hv
  have h₃ := stepH_active ambient rest f.arity h₂ ha hr
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, List.map_cons,
    AFrame.toFrame, AFrame.arity]
  rw [decodeLabels_move_values _ _ _ _ heights, decodeLabels_move_values _ _ _ _ heights]
  simpa [instrContext, vals, List.append_assoc, AFrame.arity, AFrame.toFrame] using h₃

theorem global_get_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (index address : Nat) (global : globalinst)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val f.vals)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ f.vals.length)
    (hi : index < 2^32) (mapped : f.module.GLOBALS[index]? = some address)
    (found : s.GLOBALS[address]? = some global) :
    StepH (decode ⟨s, ambient,
      { f with code := .GLOBAL_GET (.mk_uN index) :: after } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := after, vals := f.vals ++ [global.VALUE] } :: rest, []⟩) := by
  have step := Spec.global_get_step s f.toFrame index address global hs hf hi mapped found
  simpa [vals,admininstr_instr] using mutable_stack_simulation s s ambient f rest
    (.GLOBAL_GET (.mk_uN index)) after f.vals [] [global.VALUE] ha hl hv hc hr heights step

theorem global_set_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (index : Nat) (front : List val) (value : val)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val front) (valueWf : wf_val value)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length)
    (hi : index < 2^32) (mapped : index < f.module.GLOBALS.length) :
    StepH (decode ⟨s, ambient,
      { f with code := .GLOBAL_SET (.mk_uN index) :: after, vals := front ++ [value] } :: rest, []⟩) []
      (decode ⟨Spec.globalWrite s f.toFrame index value, ambient,
      { f with code := after, vals := front } :: rest, []⟩) := by
  have step := Spec.global_set_step s f.toFrame index value hs hf hi valueWf mapped
  simpa [vals,admininstr_instr] using mutable_stack_simulation s
    (Spec.globalWrite s f.toFrame index value) ambient f rest
    (.GLOBAL_SET (.mk_uN index)) after front [value] [] ha hl hv hc hr heights step

end Itasca.Runtime.Abs
