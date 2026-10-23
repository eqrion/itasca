import Exec.Interp.StructuredMachine.OrdinaryHeads
import Exec.Interp.Core.Linear
namespace Exec.Interp.StructuredMachine
open Aeneas Aeneas.Std
theorem emission_numeric_pure {compiled C before after emitted} (op : Abs.Numeric.Instruction)
    (head : Interp.emission compiled C before op.source emitted after) :
    Code.LinearEmission C.LOCALS before op.source emitted after :=
  scalarEmission_numeric_pure op (FloatHeads.project (.core (.pure (.numeric op))) head)
end Exec.Interp.StructuredMachine
