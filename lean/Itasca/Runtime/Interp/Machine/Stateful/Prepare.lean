import Itasca.Runtime.Interp.State.StatefulPrepare
import Itasca.Runtime.Interp.Machine.Stateful.Projection

/-!
Source operand values at a stateful code point.

Main declarations: `point_values`. A direct consumer is `Integration.Api.StatefulMemoryGrowExecution`.
-/

namespace Itasca.Runtime.Interp.Stateful
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Spec
variable {jumpTables : List Aeneas.Std.U32}
theorem point_values {emission : Machine.ContextEmission} {pairs C returns code labels pc next output}
    [Machine.StatefulProjection emission pairs]
    (s : store) (f : SourceMachine.AFrame) (op : SourceMachine.Stateful.Instruction) (after : List instr)
    (typed : SourceMachine.FrameTyped s {f with code:=op.source::after} [])
    (point : Compiler.StructuredCode.Point (emission C) C.TYPES C.FUNCS returns C.LOCALS
      code jumpTables labels (f.vals.map Compiler.valueType) (op.source::after) pc next output) :
    (∃ target : U32, pc<target.val ∧ code[pc]?=some (.Jump target) ∧
      Compiler.StructuredCode.Point (emission C) C.TYPES C.FUNCS returns C.LOCALS
        code jumpTables labels (f.vals.map Compiler.valueType) (op.source::after) target.val next output) ∨
    (∃ front operands input result first second a b entry,
      f.vals=front++operands ∧ operands.map Compiler.valueType=input ∧
      SourceMachine.Stateful.Signature C op input result ∧
      (∀ label ∈ f.labels,label.height≤front.length) ∧
      (∀ value ∈ operands,Val_ok s value (Compiler.valueType value)) ∧
      first.val=Compiler.slots C.LOCALS+Compiler.slots (front.map Compiler.valueType) ∧
      (op.arity≥2 → second.val=first.val+1) ∧ Compiler.StatefulArguments op a b ∧
      Compiler.StatefulPair pairs op a b entry ∧ code[pc]?=some (Compiler.statefulInstruction op first second a entry) ∧
      Compiler.StructuredCode.Point (emission C) C.TYPES C.FUNCS returns C.LOCALS
        code jumpTables labels (front.map Compiler.valueType++result) after (pc+1) next output) := by
  rcases point_head (pairs:=pairs) op after point with jump | operation
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
        simpa only [value_type_eq_abs] using SourceMachine.results_typed_self_mem actualValues included
    · simpa only [frontTypes] using position
    · simpa only [frontTypes] using tail
end Itasca.Runtime.Interp.Stateful
