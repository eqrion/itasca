import Exec.Abs.TypedSelect.Step
import Exec.Abs.BrTableTransition
import Exec.Abs.Sim.ChosenBasic
namespace Exec.Abs.TypedSelect
open SpecExt Exec.Spec

theorem Step.chosen {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) {before next}
    (step : Step before next) (typed : CoreTyped before) :
    ChoiceStep choices occurrence (decode before) [] (decode next) := by
  have source := (step.correct typed).2
  cases step
  exact chosen_neutral_simulation admissible vector occurrence source
    (by simp only [List.map_cons,admininstr_instr,neutralActive])
end Exec.Abs.TypedSelect
namespace Exec.Abs.BrTable
open SpecExt Exec.Spec

theorem chosen_correct {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr) (front : List val) (bits : Nat) (labels : List labelidx) (fallback : labelidx)
    (bound : bits < 2^32)
    (typed : ATyped ⟨s,ambient,{f with code := .BR_TABLE labels fallback :: after, vals := front ++ [integerVal .I32 bits]}::rest,[]⟩) :
    ATyped ⟨s,ambient,{f with code := .BR (select labels fallback bits)::after,vals := front}::rest,[]⟩ ∧
    ChosenNextSim choices occurrence ⟨s,ambient,{f with code := .BR_TABLE labels fallback :: after, vals := front ++ [integerVal .I32 bits]}::rest,[]⟩
      ⟨s,ambient,{f with code := .BR (select labels fallback bits)::after,vals := front}::rest,[]⟩ := by
  have frameTyped : FrameTyped s {f with code := .BR_TABLE labels fallback :: after, vals := front ++ [integerVal .I32 bits]} [] := by
    cases typed.frames with | cons head _ => exact head
  have restWf : Forall FrameWf rest := by
    cases typed.frames with | cons _ tail => exact framesTyped_wf tail
  obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frameTyped_wf frameTyped
  have afterWf : Forall wf_instr after := fun i member => codeWf i (List.mem_cons_of_mem _ member)
  have opWf := codeWf (.BR_TABLE labels fallback) (List.mem_cons_self ..)
  have frontWf : Forall wf_val front := fun v member => valuesWf v (List.mem_append_left _ member)
  have heights : ∀ label ∈ f.labels, label.height ≤ front.length := by
    obtain ⟨C,first,operands,ins,outs,bindings,locals,head,split,operandTypes,firstWf,bounds⟩ := frame_typed_operands_bounds (f := {f with vals := front ++ [integerVal .I32 bits]}) frameTyped
    cases head with
    | br_table =>
      have sizes := congrArg List.length split
      have operandSizes := operandTypes.length_eq
      simp only [List.length_append,List.length_singleton] at sizes operandSizes
      intro label member
      have small := bounds label member
      omega
  exact ⟨active_frame_preservation typed (frame_preservation frameTyped) rfl,
    ChosenNextSim.neutral admissible vector occurrence (simulation s ambient f rest after front bits labels fallback typed.store typed.ambient
      frameWf labelsWf frontWf afterWf restWf heights bound opWf)
      (by simp only [List.map_cons,admininstr_instr,neutralActive])⟩

private theorem normalized {f : AFrame} {source : List instr} {values : List val}
    (same : f.vals = values) : {f with code := source,vals := values} = {f with code := source} := by
  cases f
  simp_all

theorem Transition.chosen {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) {before next} (transition : Transition before next) (typed : CoreTyped before) :
    CoreTyped next ∧ ChosenNextSim choices occurrence before next := by
  cases transition with
  | @next s ambient f rest after labels fallback front bits values bound =>
    have result := BrTable.chosen_correct admissible vector occurrence s ambient f rest after front bits labels fallback bound
      (by simpa only [normalized values] using typed.typed)
    exact ⟨⟨result.1,typed.contents⟩,by simpa only [normalized values] using result.2⟩

end Exec.Abs.BrTable
