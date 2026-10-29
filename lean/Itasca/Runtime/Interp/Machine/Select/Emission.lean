import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Runtime.Compiler.Local.Control.Segments.Structured
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredComposition
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Interp.Control.StructuredPoint
import Itasca.Runtime.SourceMachine.ModuleBindingsExtension
import Itasca.Runtime.SourceMachine.Numeric.Decode

/-!
Scalar-emission inversion for untyped select.

Main declarations: `linear_emission_not_select` and `scalar_emission_select_inv`. A direct consumer is `Interp.Machine.Select`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem linear_emission_not_select {locals before after emitted}
    (emission : Compiler.LinearEmission locals before (.SELECT none) emitted after) : False := by
  generalize equality : instr.SELECT none = instruction at emission
  cases emission with
  | binary stack ty op a b left right => cases op <;> simp [Compiler.IntegerBinary.source] at equality
  | numeric stack op a b left right =>
    have decoded := congrArg SourceMachine.Numeric.decodeInstruction equality
    rw [SourceMachine.Numeric.decode_instruction_source] at decoded
    simp [SourceMachine.Numeric.decodeInstruction] at decoded
  | _ => cases equality

theorem scalar_emission_select_inv {C before after emitted}
    (emission : Compiler.ScalarEmission C before (.SELECT none) emitted after) :
    ∃ front ty left right condition, before = front ++ [ty,ty,.I32] ∧
      emitted = [Compiler.selectInstruction (decide (Compiler.width ty = 2)) left right condition] ∧
      after = front ++ [ty] ∧ left.val = Compiler.slots C.LOCALS+Compiler.slots front ∧
      right.val = left.val+Compiler.width ty ∧ condition.val = right.val+Compiler.width ty := by
  generalize equality : instr.SELECT none = instruction at emission
  cases emission with
  | linear pure => rw [← equality] at pure; exact False.elim (linear_emission_not_select pure)
  | select stack ty left right condition leftPos rightPos conditionPos => exact ⟨stack,ty,left,right,condition,rfl,rfl,rfl,leftPos,rightPos,conditionPos⟩
  | float stack other => cases other <;> simp [SourceMachine.Float.Instruction.source,SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at equality
  | _ => simp [SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at equality

end Itasca.Runtime.Interp
