import Itasca.Runtime.Interp.Simd.Relations.ValueSlots
import Itasca.Runtime.Spec.Simd.PureValues
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdSourceShape

/-!
Source values represented by SIMD operand slots.

Main declarations: `WordsAt.simd_value` and `ValuesAt.simd_operands`. A direct consumer is `Interp.Simd.Execution.LaneValuesExecute`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt.Builtins SpecExt.Builtins.Float

theorem WordsAt.simd_value {words : List U64} {position : Nat} {value : val}
    (represented : WordsAt words position (Compiler.encodeValue value))
    (wellFormed : wf_val value)
    (numeric : Compiler.valueType value ≠ .FUNCREF ∧ Compiler.valueType value ≠ .EXTERNREF) :
    Spec.Simd.valueOfBits (Compiler.valueType value)
      (simdInput words position (Compiler.simdSourceWidth (some (Compiler.valueType value)))).bv = value := by
  cases wellFormed with
  | val_case_0 ty num formed =>
    cases formed with
    | num__case_0 kind bits _ bounded typed =>
      subst ty
      cases bits with
      | mk_uN n =>
        have input := represented.simd_scalar 1#u32 (by decide)
        cases kind <;> cases bounded
        all_goals simp only [Spec.Simd.valueOfBits,Compiler.valueType,valtype_numtype,valtype_Inn,numtype_Inn,Compiler.simdSourceWidth,
          BitVec.toNat_setWidth,UScalar.bv_toNat]
        all_goals rw [input]
        all_goals norm_num [size,valtype_Inn] at *
        all_goals omega
    | num__case_1 kind number formed typed =>
      subst ty
      cases kind
      all_goals have input := represented.simd_scalar 1#u32 (by decide)
      all_goals simp only [Spec.Simd.valueOfBits,Compiler.valueType,valtype_numtype,valtype_Fnn,numtype_Fnn,Compiler.simdSourceWidth,
        BitVec.toNat_setWidth,UScalar.bv_toNat]
      all_goals rw [input]
      all_goals change val.CONST _ (.mk_num__1 _ (floatOfBits _ (floatBits _ number % _))) = _
      all_goals simp only [sizenn,numtype_Fnn,valtype_numtype,size,Option.get!] at *
      all_goals first
        | rw [Nat.mod_eq_of_lt (floatBits_lt_32 number formed),float_roundtrip_32 number formed]
        | rw [Nat.mod_eq_of_lt (floatBits_lt_64 number formed),float_roundtrip_64 number formed]
  | val_case_1 ty bits sized bounded =>
    cases ty
    cases bits with
    | mk_uN n =>
      have input := represented.simd_vector
      change val.VCONST .V128 (.mk_uN (simdInput words position 2#u32).val) = _
      rw [input]
  | val_case_2 ty => cases ty <;> simp [Compiler.valueType] at numeric
  | val_case_3 => simp [Compiler.valueType] at numeric
  | val_case_4 => simp [Compiler.valueType] at numeric

theorem simd_source_width_value (ty : valtype) :
    (Compiler.simdSourceWidth (some ty)).val = Compiler.width ty := by
  cases ty <;> rfl

theorem ValuesAt.simd_operands {words : List U64} {base : Nat} {values : List val}
    (represented : ValuesAt words base values) (wellFormed : Forall wf_val values)
    (numeric : ∀ value ∈ values, Compiler.valueType value ≠ .FUNCREF ∧ Compiler.valueType value ≠ .EXTERNREF)
    (arity : values.length ≤ 3) :
    let types := values.map Compiler.valueType
    let wa := Compiler.simdSourceWidth types[0]?
    let wb := Compiler.simdSourceWidth types[1]?
    let wc := Compiler.simdSourceWidth types[2]?
    Spec.Simd.operandValues types (simdInput words base wa).bv
      (simdInput words (base+wa.val) wb).bv
      (simdInput words (base+wa.val+wb.val) wc).bv = values := by
  have each {i : Nat} {value : val} (found : values[i]? = some value) :=
    (represented.lookup found).simd_value (wellFormed value (List.mem_of_getElem? found))
      (numeric value (List.mem_of_getElem? found))
  cases values with
  | nil => rfl
  | cons v rest =>
    have first := each (i := 0) (value := v) (by simp)
    cases rest with
    | nil =>
      simpa [Spec.Simd.operandValues,Compiler.offset,Compiler.slots] using congrArg (fun value => [value]) first
    | cons w rest =>
      have second := each (i := 1) (value := w) (by simp)
      cases rest with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.getElem?_cons_zero,List.getElem?_cons_succ,List.getElem?_nil,
          Spec.Simd.operandValues,List.zipWith_cons_cons,List.zipWith_nil_right,List.zipWith_nil_left]
        simp only [List.map_cons,List.map_nil,Compiler.offset,List.take_succ_cons,List.take_zero,Compiler.slots,Nat.add_zero] at first second
        rw [first,simd_source_width_value,second]
      | cons u rest =>
        have third := each (i := 2) (value := u) (by simp)
        have empty : rest = [] := by
          cases rest with
          | nil => rfl
          | cons next tail => simp only [List.length_cons] at arity; omega
        subst rest
        simp only [List.map_cons,List.map_nil,List.getElem?_cons_zero,List.getElem?_cons_succ,
          Spec.Simd.operandValues,List.zipWith_cons_cons,List.zipWith_nil_right,List.zipWith_nil_left]
        simp only [List.map_cons,List.map_nil,Compiler.offset,List.take_succ_cons,List.take_zero,Compiler.slots,Nat.add_zero] at first second third
        rw [first,simd_source_width_value,second,simd_source_width_value]
        rw [←Nat.add_assoc] at third
        rw [third]
end Itasca.Runtime.Interp
