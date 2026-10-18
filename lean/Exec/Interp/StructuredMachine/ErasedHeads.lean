import Exec.Interp.FloatCore.Linear
import Exec.Interp.StructuredMachine.StatefulHeads
namespace Exec.Interp.StructuredMachine

/-- Erased source operations emit exactly their existing empty linear fragments. -/
class ErasedHeads (emission : ContextEmission) : Prop where
  nop : ∀ {C before after emitted}, emission C before .NOP emitted after →
    Code.LinearEmission C.LOCALS before .NOP emitted after
  drop : ∀ {C before after emitted}, emission C before .DROP emitted after →
    Code.LinearEmission C.LOCALS before .DROP emitted after

instance : ErasedHeads Code.CoreEmission := ⟨coreEmission_nop_pure,coreEmission_drop_pure⟩
instance : ErasedHeads Code.FloatCoreEmission := ⟨floatCoreEmission_nop_pure,floatCoreEmission_drop_pure⟩

instance {pairs} : ErasedHeads (Code.StatefulEmission pairs) where
  nop := by
    intro C before after emitted head
    generalize equality : instr.NOP = instruction at head
    cases head with
    | instruction stack input output op signature first second a b entry firstSlot secondSlot arguments pair =>
      cases op <;> cases equality
  drop := by
    intro C before after emitted head
    generalize equality : instr.DROP = instruction at head
    cases head with
    | instruction stack input output op signature first second a b entry firstSlot secondSlot arguments pair =>
      cases op <;> cases equality

instance {left right : ContextEmission} [ErasedHeads left] [ErasedHeads right] :
    ErasedHeads (Code.EmissionUnion left right) where
  nop := by
    intro C before after emitted head
    cases head with
    | left h => exact ErasedHeads.nop h
    | right h => exact ErasedHeads.nop h
  drop := by
    intro C before after emitted head
    cases head with
    | left h => exact ErasedHeads.drop h
    | right h => exact ErasedHeads.drop h
instance {pairs} : ErasedHeads (Code.CumulativeEmission pairs) where
  nop := by
    intro C before after emitted head
    cases head with
    | left h => exact ErasedHeads.nop h
    | right h => exact ErasedHeads.nop h
    | indirect h => cases h
  drop := by
    intro C before after emitted head
    cases head with
    | left h => exact ErasedHeads.drop h
    | right h => exact ErasedHeads.drop h
    | indirect h => cases h

end Exec.Interp.StructuredMachine
