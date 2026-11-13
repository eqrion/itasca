import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Runtime.Compiler.Local.Control.Segments.Structured
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredComposition
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.SourceMachine.Measure
import Itasca.Runtime.SourceMachine.Numeric.Decode
import Itasca.Runtime.SourceMachine.Core.Trap

/-!
Sections, each formerly its own module: Emission, Operands.
-/

/-! ## Emission -/

section

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

end

/-! ## Operands -/

section

/-!
Typed select operands and the corresponding source successor.

Main declarations: `select_typed_operands` and `select_source_next`. A direct consumer is `Interp.Machine.Select`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem select_typed_operands {s : _root_.store} {f : SourceMachine.AFrame} {after : List instr}
    (typed : SourceMachine.FrameTyped s {f with code := .SELECT none::after} []) :
    ∃ front left right bits ty,
      f.vals = front ++ [left,right,SourceMachine.integerVal .I32 bits] ∧ bits < 2^32 ∧
      Compiler.valueType left = ty ∧ Compiler.valueType right = ty ∧
      (∀ label ∈ f.labels, label.height ≤ front.length) := by
  obtain ⟨C,front,operands,ins,outs,_,_,operation,split,operandTypes,frontWf,heights⟩ :=
    SourceMachine.frame_typed_operands_bounds typed
  cases operation
  cases operandTypes with
  | cons leftTyped tail =>
    cases tail with
    | cons rightTyped tail =>
      cases tail with
      | cons conditionTyped tail =>
        cases tail
        rename_i left right condition
        obtain ⟨bits,rfl,bitsBound⟩ := SourceMachine.integer_val_inv (ty := .I32) conditionTyped
        exact ⟨front,left,right,bits,_,split,bitsBound,
          (value_type_eq_abs left).trans (SourceMachine.value_type_of_typed leftTyped),
          (value_type_eq_abs right).trans (SourceMachine.value_type_of_typed rightTyped),heights⟩

theorem select_source_next {s : _root_.store} {ambient : frame} {f : SourceMachine.AFrame} {rest : List SourceMachine.AFrame}
    {after : List instr} {front : List val} {left right : val} {bits : Nat}
    (values : f.vals = front ++ [left,right,SourceMachine.integerVal .I32 bits])
    (matching : Compiler.valueType left = Compiler.valueType right) (bounded : bits < 2^32) :
    SourceMachine.Core.step ⟨s,ambient,{f with code := .SELECT none::after}::rest,[]⟩ =
      .next ⟨s,ambient,{f with code := after,vals := front ++ [if bits = 0 then right else left]}::rest,[]⟩ := by
  have shape : f.vals = ((front ++ [left]) ++ [right]) ++ [SourceMachine.integerVal .I32 bits] := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using values
  have decoded : SourceMachine.integer .I32 (SourceMachine.integerVal .I32 bits) = some bits := by
    simpa only [numtype_Inn] using SourceMachine.integer_accepts .I32 bits bounded
  have types : SourceMachine.valueType left = SourceMachine.valueType right := by simpa only [value_type_eq_abs] using matching
  simp only [SourceMachine.Core.step,SourceMachine.Core.instruction,SourceMachine.Core.select,shape,SourceMachine.pop_append,decoded,types,
    ite_true,SourceMachine.advance]
end Itasca.Runtime.Interp

end
