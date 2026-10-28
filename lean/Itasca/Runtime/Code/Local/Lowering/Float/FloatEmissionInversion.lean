import Itasca.Runtime.Abs.Float.Decode
import Itasca.Runtime.Code.Local.Relations.Common.ScalarEmission
namespace Itasca.Runtime.Code
open Aeneas.Std

theorem LinearEmission.float_decode_none {locals before instruction emitted after}
    (emission : LinearEmission locals before instruction emitted after) :
    Abs.Float.decodeInstruction instruction = none := by
  cases emission with
  | binary stack ty op => cases ty <;> cases op <;> rfl
  | numeric stack op =>
    cases op with
    | binary ty operator => cases ty <;> rfl
    | compare ty operator => cases ty <;> rfl
    | unary ty operator => cases ty <;> cases operator <;> rfl
    | eqz ty => cases ty <;> rfl
    | conversion operator => cases operator <;> rfl
  | _ => rfl

theorem ScalarEmission.float_inv {C before emitted after}
    (op : Abs.Float.Instruction)
    (emission : ScalarEmission C before op.source emitted after) :
    ∃ stack left right,
      before = stack ++ List.replicate op.arity (valtype_numtype op.input) ∧
      after = stack ++ [valtype_numtype op.output] ∧
      emitted = [floatInstruction op left left right] ∧
      left.val = slots C.LOCALS + slots stack ∧
      right.val = left.val + (op.arity - 1) := by
  generalize sourceEq : op.source = instruction at emission
  cases emission with
  | linear h =>
    have impossible := h.float_decode_none
    rw [← sourceEq, Abs.Float.decodeInstruction_source] at impossible
    contradiction
  | float stack selected left right leftSlot rightSlot =>
    have same : op = selected := Abs.Float.Instruction.source_injective sourceEq
    subst selected
    exact ⟨stack,left,right,rfl,rfl,rfl,leftSlot,rightSlot⟩
  | _ =>
    have decoded := congrArg Abs.Float.decodeInstruction sourceEq
    rw [Abs.Float.decodeInstruction_source] at decoded
    simp [Abs.Float.decodeInstruction,Abs.Memory.Load.source,Abs.Memory.Store.source] at decoded
end Itasca.Runtime.Code
