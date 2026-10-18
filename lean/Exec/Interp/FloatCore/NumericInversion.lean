import Exec.Interp.FloatCore.Linear
namespace Exec.Interp
open Aeneas.Std

theorem integer_source_not_float (op : Abs.Numeric.Instruction) :
    Abs.Float.decodeInstruction op.source = none := by
  cases op with
  | binary ty operation => cases ty <;> rfl
  | unary ty operation => cases ty <;> cases operation <;> rfl
  | compare ty operation => cases ty <;> rfl
  | eqz ty => cases ty <;> rfl
  | conversion operation => cases operation <;> rfl

theorem floatCoreEmission_numeric_pure {C before after emitted} (op : Abs.Numeric.Instruction)
    (emission : Code.FloatCoreEmission C before op.source emitted after) :
    Code.LinearEmission C.LOCALS before op.source emitted after :=
  coreEmission_numeric_pure op (emission.core_inv (integer_source_not_float op))
end Exec.Interp
