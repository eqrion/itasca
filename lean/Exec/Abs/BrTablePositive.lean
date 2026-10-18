import Exec.Abs.BrTableTransition
namespace Exec.Abs.BrTable
open SpecExt Exec.Spec
theorem positive (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr) (front : List val) (bits : Nat) (labels : List labelidx) (fallback : labelidx)
    (bound : bits < 2^32)
    (typed : ATyped ⟨s,ambient,{f with code := .BR_TABLE labels fallback :: after, vals := front ++ [integerVal .I32 bits]}::rest,[]⟩) :
    StepH (decode ⟨s,ambient,{f with code := .BR_TABLE labels fallback :: after, vals := front ++ [integerVal .I32 bits]}::rest,[]⟩) []
      (decode ⟨s,ambient,{f with code := .BR (select labels fallback bits)::after,vals := front}::rest,[]⟩) := by
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
  exact simulation s ambient f rest after front bits labels fallback typed.store typed.ambient
      frameWf labelsWf frontWf afterWf restWf heights bound opWf

theorem Transition.positive {before next} (transition : Transition before next) (typed : CoreTyped before) :
    StepH (decode before) [] (decode next) := by
  cases transition with
  | @next s ambient f rest after labels fallback front bits values bound =>
    have normalized : {f with code := .BR_TABLE labels fallback::after, vals := front ++ [integerVal .I32 bits]} =
        {f with code := .BR_TABLE labels fallback::after} := by cases f; simp_all
    simpa only [normalized] using BrTable.positive s ambient f rest after front bits labels fallback bound
      (by simpa only [normalized] using typed.typed)
end Exec.Abs.BrTable
