import Itasca.Runtime.Abs.Stateful.Signature
import Itasca.Runtime.Abs.Safety
namespace Itasca.Runtime.Abs.Stateful
open SpecExt Itasca.Runtime.Spec

private theorem lookup_eq {α : Type} [Inhabited α] (values : List α) (index : Nat) (value : α)
    (bound : index < values.length) (read : values[index]! = value) : values[index]? = some value := by
  simpa only [getElem!_pos values index bound, List.getElem?_eq_getElem bound] using congrArg some read

theorem Signature.of_typed {C : context} {op : Instruction} {input output : List valtype}
    (typed : Instr_ok C op.source ⟨.mk_list input,.mk_list output⟩) : Signature C op input output := by
  cases op <;> simp only [Instruction.source] at typed <;> cases typed
  all_goals first
    | constructor
  all_goals first
    | assumption
    | (apply lookup_eq <;> assumption)

end Itasca.Runtime.Abs.Stateful
