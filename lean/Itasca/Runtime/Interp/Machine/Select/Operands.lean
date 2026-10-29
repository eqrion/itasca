import Itasca.Runtime.SourceMachine.Core.Select
import Itasca.Runtime.SourceMachine.Core.Step
import Itasca.Runtime.Interp.Machine.Select.Emission

/-!
Typed select operands and the corresponding source successor.

Main declarations: `select_typed_operands` and `select_source_next`. A direct consumer is `Interp.Machine.Select`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem select_typed_operands {s : _root_.store} {f : Abs.AFrame} {after : List instr}
    (typed : Abs.FrameTyped s {f with code := .SELECT none::after} []) :
    ∃ front left right bits ty,
      f.vals = front ++ [left,right,Abs.integerVal .I32 bits] ∧ bits < 2^32 ∧
      Code.valueType left = ty ∧ Code.valueType right = ty ∧
      (∀ label ∈ f.labels, label.height ≤ front.length) := by
  obtain ⟨C,front,operands,ins,outs,_,_,operation,split,operandTypes,frontWf,heights⟩ :=
    Abs.frame_typed_operands_bounds typed
  cases operation
  cases operandTypes with
  | cons leftTyped tail =>
    cases tail with
    | cons rightTyped tail =>
      cases tail with
      | cons conditionTyped tail =>
        cases tail
        rename_i left right condition
        obtain ⟨bits,rfl,bitsBound⟩ := Abs.integer_val_inv (ty := .I32) conditionTyped
        exact ⟨front,left,right,bits,_,split,bitsBound,
          (valueType_eq_abs left).trans (Abs.value_type_of_typed leftTyped),
          (valueType_eq_abs right).trans (Abs.value_type_of_typed rightTyped),heights⟩

theorem select_source_next {s : _root_.store} {ambient : frame} {f : Abs.AFrame} {rest : List Abs.AFrame}
    {after : List instr} {front : List val} {left right : val} {bits : Nat}
    (values : f.vals = front ++ [left,right,Abs.integerVal .I32 bits])
    (matching : Code.valueType left = Code.valueType right) (bounded : bits < 2^32) :
    Abs.Core.step ⟨s,ambient,{f with code := .SELECT none::after}::rest,[]⟩ =
      .next ⟨s,ambient,{f with code := after,vals := front ++ [if bits = 0 then right else left]}::rest,[]⟩ := by
  have shape : f.vals = ((front ++ [left]) ++ [right]) ++ [Abs.integerVal .I32 bits] := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using values
  have decoded : Abs.integer .I32 (Abs.integerVal .I32 bits) = some bits := by
    simpa only [numtype_Inn] using Abs.integer_accepts .I32 bits bounded
  have types : Abs.valueType left = Abs.valueType right := by simpa only [valueType_eq_abs] using matching
  simp only [Abs.Core.step,Abs.Core.instruction,Abs.Core.select,shape,Abs.pop_append,decoded,types,
    ite_true,Abs.advance]
end Itasca.Runtime.Interp
