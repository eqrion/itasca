import Exec.Abs.Float.Operands
import Exec.Abs.Preservation
namespace Itasca.Runtime.Abs.Float
open SpecExt Itasca.Runtime.Spec SpecExt.Builtins SpecExt.Builtins.Float

theorem Instruction.source_signature_inv (op : Instruction) {C : context} {signature : functype}
    (typed : Instr_ok C op.source signature) : signature = op.signature := by
  cases op <;> cases typed <;> rfl

theorem Instruction.operands_types (op : Instruction) (a b : Nat) :
    (op.operands a b).map valueType = List.replicate op.arity (valtype_numtype op.input) := by
  cases op <;> rfl

theorem Instruction.frame_preservation (op : Instruction) {s : store} {f : AFrame} {after : List instr}
    (front : List val) (a b bits : Nat) (storeWf : wf_store s)
    (bound : bits < 2^sizenn op.output)
    (typed : FrameTyped s { f with code := op.source :: after, vals := front ++ op.operands a b } []) :
    FrameTyped s { f with code := after, vals := front ++ [.CONST op.output (numberOfBits op.output bits)] } [] := by
  cases typed with
  | mk C bindings localTypes locals values returns code contextWf =>
    simp only [List.append_nil] at code
    obtain ⟨prefixTypes, ins, outs, instruction, stack, continuation⟩ :=
      codeStack_after (value_types_concrete (front ++ op.operands a b)) code
    have signature := op.source_signature_inv instruction
    simp only [Instruction.signature, functype.mk_functype.injEq, list.mk_list.injEq] at signature
    rcases signature with ⟨rfl, rfl⟩
    simp only [List.map_append, operands_types, List.append_cancel_right_eq] at stack
    have frontTyped : ResultsTyped s (front.map valueType) front := by
      simpa using resultsTyped_take front.length values
    have resultTyped := numberOfBits_typed s storeWf op.output bits bound
    apply FrameTyped.mk (f := { f with code := after, vals := front ++ [.CONST op.output (numberOfBits op.output bits)] }) C
      bindings localTypes locals ?_ returns ?_ contextWf
    · simpa only [ResultsTyped, List.map_append, List.map_cons, List.map_nil, valueType] using
        List.rel_append frontTyped (List.Forall₂.cons resultTyped List.Forall₂.nil)
    · simpa only [List.map_append, List.map_cons, List.map_nil, List.append_nil, valueType, stack] using continuation

end Itasca.Runtime.Abs.Float
