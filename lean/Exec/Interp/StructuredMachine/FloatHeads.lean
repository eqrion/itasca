import Exec.Interp.StructuredMachine.IndirectHeads
import Exec.Interp.StructuredMachine.StatefulHeads
import Exec.Abs.FloatCore
namespace Exec.Interp.StructuredMachine

/-- Projection of a retained legacy scalar head, independent of the following
source program. This permits reuse inside a larger instruction family. -/
class FloatHeads (emission : ContextEmission) : Prop where
  project : ∀ {C before instruction emitted after}, Abs.FloatCoreInstr instruction →
    emission C before instruction emitted after → Code.FloatCoreEmission C before instruction emitted after

instance : FloatHeads Code.FloatCoreEmission where
  project _ head := head

private theorem slice_stateful_none {instruction} (covered : Abs.SliceInstr instruction) :
    Abs.Stateful.decodeInstruction instruction = none := by
  cases covered with
  | numeric op => cases op <;> rfl
  | _ => rfl

private theorem core_stateful_none {instruction} (covered : Abs.CoreInstr instruction) :
    Abs.Stateful.decodeInstruction instruction = none := by
  cases covered with
  | slice h => exact slice_stateful_none h
  | load op argument => cases op <;> rfl
  | store op argument => cases op <;> rfl
  | _ => rfl

private theorem float_stateful_none {instruction} (covered : Abs.FloatCoreInstr instruction) :
    Abs.Stateful.decodeInstruction instruction = none := by
  cases covered with
  | core h => exact core_stateful_none h
  | scalar op => cases op <;> rfl
  | _ => rfl

instance {pairs} : FloatHeads (Code.CumulativeEmission pairs) where
  project := by
    intro C before instruction emitted after covered head
    cases head with
    | indirect h => cases h; exact False.elim (float_core_not_indirect covered)
    | left h => exact h
    | right h =>
      cases h with
      | instruction stack input output op signature first second a b entry firstSlot secondSlot arguments pair =>
        have impossible := float_stateful_none covered
        rw [Abs.Stateful.decode_source] at impossible
        cases impossible
end Exec.Interp.StructuredMachine
