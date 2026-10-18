import Exec.Interp.StructuredMachine.HeadInstances
import Exec.Code.Local.Relations.Common.StatefulEmission
namespace Exec.Interp.StructuredMachine

instance {pairs} : OrdinaryHeads (Code.StatefulEmission pairs) where
  ordinary := by
    intro C before instruction emitted after head
    cases head with
    | instruction stack input output op signature first second a b entry firstSlot secondSlot arguments pair =>
      cases op <;> rfl

instance {left right : ContextEmission} [OrdinaryHeads left] [OrdinaryHeads right] :
    OrdinaryHeads (Code.EmissionUnion left right) where
  ordinary := by
    intro C before instruction emitted after head
    cases head with
    | left h => exact OrdinaryHeads.ordinary h
    | right h => exact OrdinaryHeads.ordinary h

instance {pairs} : OrdinaryHeads (Code.CumulativeEmission pairs) where
  ordinary := by
    intro C before instruction emitted after head
    cases head with
    | left h => exact OrdinaryHeads.ordinary h
    | right h => exact OrdinaryHeads.ordinary h
    | indirect h => cases h; rfl

end Exec.Interp.StructuredMachine
