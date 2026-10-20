import Exec.Abs.Sim.ChosenContext
import Exec.Spec.Choices.ChosenRedexWf
namespace Exec.Abs
open SpecExt Exec.Spec

/-- A selected numeric reply changes the decoded operand stack through every
label and caller with exactly one source occurrence. -/
theorem chosen_numeric_stack {choices : SourceChoices} (admissible : choices.Admissible) {occurrence : Nat}
    {request : NumericRequest} {reply : Option num_} (chosen : ChosenNumeric choices.numeric occurrence request reply)
    (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame) (instruction : instr) (after : List instr)
    (front consumed produced : List val) (storeWf : wf_store s) (ambientWf : wf_frame ambient)
    (frameWf : wf_frame f.toFrame) (labelsWf : LabelsWf f.labels) (frontWf : Forall wf_val front)
    (afterWf : Forall wf_instr after) (restWf : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height≤front.length)
    (input : request.instructions=vals consumed++[admininstr_instr instruction]) (output : numericOutput request.type reply=vals produced) :
    ChoiceStep choices occurrence
      (decode ⟨s,ambient,{f with code := instruction::after,vals := front++consumed}::rest,[]⟩) []
      (decode ⟨s,ambient,{f with code := after,vals := front++produced}::rest,[]⟩) := by
  apply choice_stack_simulation admissible s ambient f rest instruction after front consumed produced
    ambientWf labelsWf frontWf afterWf restWf heights
  have root := chosen.step admissible s f.toFrame storeWf frameWf
  simpa only [input,output] using root

/-- A selected vector reply changes the decoded operand stack through every
label and caller with exactly one source occurrence. -/
theorem chosen_vector_stack {choices : SourceChoices} (admissible : choices.Admissible) {occurrence : Nat}
    {request : VectorRequest} {reply : Option vec_} (chosen : ChosenVector choices.vector occurrence request reply)
    (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame) (instruction : instr) (after : List instr)
    (front consumed produced : List val) (storeWf : wf_store s) (ambientWf : wf_frame ambient)
    (frameWf : wf_frame f.toFrame) (labelsWf : LabelsWf f.labels) (frontWf : Forall wf_val front)
    (afterWf : Forall wf_instr after) (restWf : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height≤front.length)
    (input : request.instructions=vals consumed++[admininstr_instr instruction]) (output : vectorOutput reply=vals produced) :
    ChoiceStep choices occurrence
      (decode ⟨s,ambient,{f with code := instruction::after,vals := front++consumed}::rest,[]⟩) []
      (decode ⟨s,ambient,{f with code := after,vals := front++produced}::rest,[]⟩) := by
  apply choice_stack_simulation admissible s ambient f rest instruction after front consumed produced
    ambientWf labelsWf frontWf afterWf restWf heights
  have root := chosen.step admissible s f.toFrame storeWf frameWf
  simpa only [input,output] using root
end Exec.Abs
