import Exec.Interp.State.StatefulPoint
import Exec.Abs.Stateful.Continuation
import Exec.Abs.Stateful.SignatureTyping
namespace Exec.Interp.Stateful
open Aeneas Aeneas.Std SpecExt Exec.Spec

theorem operand_heights {s : store} {f : Abs.AFrame} {op : Abs.Stateful.Instruction} {after : List instr}
    (typed : Abs.FrameTyped s {f with code:=op.source::after} [])
    (front operands : List val) (values : f.vals=front++operands) (arity : operands.length=op.arity) :
    ∀ label ∈ f.labels, label.height≤front.length := by
  obtain ⟨C,actualFront,actualOperands,inputs,outputs,bindings,locals,operation,split,operandTypes,wf,heights,continuation⟩ := Abs.Stateful.frame_operands typed
  have actualArity := (Abs.Stateful.Signature.of_typed operation).input_length
  have operandLength := resultsTyped_length operandTypes
  have lengths := congrArg List.length (values.symm.trans split)
  simp only [List.length_append] at lengths
  intro label member
  have height := heights label member
  omega

theorem cumulative_point_values {pairs C returns code labels pc next output}
    (s : store) (f : Abs.AFrame) (op : Abs.Stateful.Instruction) (after : List instr)
    (typed : Abs.FrameTyped s {f with code:=op.source::after} [])
    (point : Code.StructuredCode.Point (Code.CumulativeEmission pairs C) C.TYPES C.FUNCS returns C.LOCALS
      code labels (f.vals.map Code.valueType) (op.source::after) pc next output) :
    (∃ target : U32, pc<target.val ∧ code[pc]?=some (.Jump target) ∧
      Code.StructuredCode.Point (Code.CumulativeEmission pairs C) C.TYPES C.FUNCS returns C.LOCALS
        code labels (f.vals.map Code.valueType) (op.source::after) target.val next output) ∨
    (∃ front operands input result first second a b entry,
      f.vals=front++operands ∧ operands.map Code.valueType=input ∧
      Abs.Stateful.Signature C op input result ∧
      (∀ label ∈ f.labels,label.height≤front.length) ∧
      (∀ value ∈ operands,Val_ok s value (Code.valueType value)) ∧
      first.val=Code.slots C.LOCALS+Code.slots (front.map Code.valueType) ∧
      (op.arity≥2 → second.val=first.val+1) ∧ Code.StatefulArguments op a b ∧
      Code.StatefulPair pairs op a b entry ∧ code[pc]?=some (Code.statefulInstruction op first second a entry) ∧
      Code.StructuredCode.Point (Code.CumulativeEmission pairs C) C.TYPES C.FUNCS returns C.LOCALS
        code labels (front.map Code.valueType++result) after (pc+1) next output) := by
  rcases cumulative_point_head op after point with jump | operation
  · exact Or.inl jump
  · obtain ⟨types,input,result,first,second,a,b,entry,signature,stack,position,secondSlot,arguments,pair,fetch,tail⟩ := operation
    obtain ⟨front,operands,values,frontTypes,operandTypes⟩ := List.map_eq_append_iff.mp stack
    have arity : operands.length=op.arity := by
      have h := congrArg List.length operandTypes
      simpa only [List.length_map,signature.input_length] using h
    refine Or.inr ⟨front,operands,input,result,first,second,a,b,entry,values,operandTypes,signature,
      operand_heights typed front operands values arity,?_,?_,secondSlot,arguments,pair,fetch,?_⟩
    · intro value member
      cases typed with
      | mk context bindings localTypes locals actualValues returns code frameWf =>
        have included : value∈f.vals := by rw [values]; exact List.mem_append_right front member
        simpa only [valueType_eq_abs] using Abs.resultsTyped_self_mem actualValues included
    · simpa only [frontTypes] using position
    · simpa only [frontTypes] using tail
end Exec.Interp.Stateful
