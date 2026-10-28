import Exec.Interp.StructuredMachine.OrdinaryHeads
import Exec.Abs.Stateful.Continuation
import Exec.Abs.Stateful.SignatureTyping
namespace Itasca.Runtime.Interp.Stateful
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Spec

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

end Itasca.Runtime.Interp.Stateful
