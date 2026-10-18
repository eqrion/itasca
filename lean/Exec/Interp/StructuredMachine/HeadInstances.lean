import Exec.Interp.StructuredMachine.OrdinaryHeads
import Exec.Code.Local.Lowering.Float.FloatCoreEmission
namespace Exec.Interp.StructuredMachine

theorem linear_emission_ordinary {locals before instruction emitted after}
    (head : Code.LinearEmission locals before instruction emitted after) : ordinarySource instruction = true := by
  cases head <;> try rfl
  case binary stack ty op a b left right => cases op <;> rfl
  case numeric stack op a b left right => cases op <;> (try casesm* Abs.Numeric.Conversion) <;> rfl

instance coreOrdinaryHeads : OrdinaryHeads Code.CoreEmission where
  ordinary := by
    intro C before instruction emitted after head
    cases head <;> try rfl
    case pure h => exact linear_emission_ordinary h

instance floatCoreOrdinaryHeads : OrdinaryHeads Code.FloatCoreEmission where
  ordinary := by
    intro C before instruction emitted after head
    cases head with
    | core h => exact OrdinaryHeads.ordinary h
    | scalar stack op left right leftSlot rightSlot => cases op <;> rfl
end Exec.Interp.StructuredMachine
