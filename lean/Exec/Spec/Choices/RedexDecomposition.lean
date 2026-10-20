import Exec.Spec.Choices.CoreChoiceStep
namespace Exec.Spec
open SpecExt

theorem instructionValue_some {instruction : admininstr} {value : val}
    (read : instructionValue instruction=some value) : instruction=admininstr_val value := by
  cases instruction <;> simp only [instructionValue,Option.some.injEq] at read
  all_goals first | contradiction | (cases read; rfl)

theorem residualCode_cons (instruction : admininstr) (tail : List admininstr) :
    residualCode (instruction::tail)=if (instructionValue instruction).isSome then residualCode tail else instruction::tail := by
  cases instruction <;> rfl

theorem residual_single_decompose {code : List admininstr} (single : (residualCode code).length=1) :
    ∃ args instruction, code=vals args++[instruction] ∧ instructionValue instruction=none := by
  induction code with
  | nil => simp [residualCode] at single
  | cons instruction tail ih =>
    cases read : instructionValue instruction with
    | none =>
      have count := single
      simp only [residualCode_cons,read,Option.isSome_none,Bool.false_eq_true,ite_false,List.length_cons] at count
      have empty : tail=[] := List.length_eq_zero_iff.mp (by omega)
      cases empty
      exact ⟨[],instruction,rfl,read⟩
    | some value =>
      have representation := instructionValue_some read
      have count := single
      simp only [residualCode_cons,read,Option.isSome_some,ite_true] at count
      obtain ⟨args,operation,body,nonvalue⟩ := ih count
      refine ⟨value::args,operation,?_,nonvalue⟩
      simpa only [vals,List.map_cons,List.cons_append,representation] using congrArg (List.cons (admininstr_val value)) body

theorem CoreChoiceStep.residual_single {choices : SourceChoices} {occurrence : Nat}
    {before after : config} {events : List HostEvent}
    (source : CoreChoiceStep choices occurrence before events after)
    (nonactive : activeTrap (trapCode before)=false) : (residualCode (trapCode before)).length=1 := by
  cases source
  case ordinary_pure source free input output => exact pure_residual_single source nonactive
  case ordinary_read source input output => exact read_residual_single source
  case write source => exact source.residual_single
  case numeric => casesm* NumericRequest; all_goals rfl
  case vector => casesm* VectorRequest; all_goals rfl
  all_goals try { simp [trapCode,residualCode,residualCode_vals,Segment.i32] }
  all_goals casesm* ref
  all_goals simp [trapCode,admininstr_ref,residualCode,Segment.i32]

theorem CoreChoiceStep.operand_arity {choices : SourceChoices} {occurrence : Nat}
    {z : state} {before : List admininstr} {after : config} {events : List HostEvent}
    (source : CoreChoiceStep choices occurrence ⟨z,before⟩ events after)
    (nonactive : activeTrap before=false) :
    before.length=operandArity z (residualCode before).head!+1 := by
  cases source
  case ordinary_pure => exact pure_operand_arity _ (by assumption) nonactive
  case ordinary_read => exact read_operand_arity (by assumption)
  case write source => exact source.operand_arity
  case numeric => exact NumericRequest.operand_arity _ _
  case vector => exact VectorRequest.operand_arity _ _
  case host => exact host_operand_arity (by assumption) (by assumption)
  all_goals try { simp [operandArity,residualCode,Segment.i32] }
  all_goals casesm* ref
  all_goals simp [admininstr_ref,operandArity,residualCode,Segment.i32]

theorem residualCode_nonvalue (instruction : admininstr) (tail : List admininstr)
    (nonvalue : instructionValue instruction=none) : residualCode (instruction::tail)=instruction::tail := by
  simp only [residualCode_cons,nonvalue,Option.isSome_none,Bool.false_eq_true,ite_false]

theorem CoreChoiceStep.input_shape {choices : SourceChoices} {occurrence : Nat} {z : state}
    {before : List admininstr} {events : List HostEvent} {after : config}
    (source : CoreChoiceStep choices occurrence ⟨z,before⟩ events after)
    (nonactive : activeTrap before=false) :
    ∃ args instruction, before=vals args++[instruction] ∧ instructionValue instruction=none ∧
      args.length=operandArity z instruction := by
  obtain ⟨args,instruction,shape,nonvalue⟩ := residual_single_decompose (source.residual_single nonactive)
  dsimp only [trapCode] at shape
  have count := source.operand_arity nonactive
  rw [shape] at count
  simp only [residualCode_vals,residualCode_nonvalue _ _ nonvalue,List.head!_cons] at count
  simp only [List.length_append,vals,List.length_map,List.length_cons,List.length_nil] at count
  exact ⟨args,instruction,shape,nonvalue,by omega⟩
end Exec.Spec
