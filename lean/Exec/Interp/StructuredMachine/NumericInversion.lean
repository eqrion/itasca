import Exec.Interp.StructuredMachine.FloatHeads
import Exec.Interp.FloatCore.NumericInversion
namespace Exec.Interp.StructuredMachine
open Aeneas Aeneas.Std
variable {emission : FunctionEmission} [∀ compiled, FloatHeads (emission compiled)]
theorem emission_numeric_pure {compiled C before after emitted} (op : Abs.Numeric.Instruction)
    (head : emission compiled C before op.source emitted after) :
    Code.LinearEmission C.LOCALS before op.source emitted after :=
  floatCoreEmission_numeric_pure op (FloatHeads.project (.core (.slice (.numeric op))) head)
end Exec.Interp.StructuredMachine
