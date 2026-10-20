import Exec.Spec.Choices.RedexArity
namespace Exec.Spec
open SpecExt

theorem operand_context_unique (state : _root_.state)
    {front args otherFront otherArgs : List val} {operation otherOperation : admininstr}
    {tail otherTail : List admininstr}
    (nonvalue : instructionValue operation=none) (otherNonvalue : instructionValue otherOperation=none)
    (firstArity : args.length=operandArity state operation)
    (secondArity : otherArgs.length=operandArity state otherOperation)
    (same : vals front++((vals args++[operation])++tail)=
      vals otherFront++((vals otherArgs++[otherOperation])++otherTail)) :
    front=otherFront ∧ args=otherArgs ∧ operation=otherOperation ∧ tail=otherTail := by
  have flat : vals (front++args)++operation::tail=vals (otherFront++otherArgs)++otherOperation::otherTail := by
    simpa only [vals,List.map_append,List.append_assoc,List.singleton_append] using same
  obtain ⟨prefixEq,operationEq,tailEq⟩ := value_prefix_unique nonvalue otherNonvalue flat
  cases operationEq
  have count : args.length=otherArgs.length := firstArity.trans secondArity.symm
  have arguments := List.append_inj_right' prefixEq count
  cases arguments
  have retained := List.append_cancel_right prefixEq
  exact ⟨retained,rfl,rfl,tailEq⟩
end Exec.Spec
