import Itasca.Runtime.Interp.Simd.Execution.PureUnary
import Itasca.Runtime.Interp.Relations.ReferenceSource
import Itasca.Runtime.Interp.Simd.Relations.PureRelation
import Itasca.Runtime.Interp.Simd.Lanes.Swizzle
import Itasca.Runtime.Interp.Simd.Integer.CompareSigned
import Itasca.Runtime.Spec.ModuleMembership
import Itasca.Runtime.Spec.FloatTrunc
import Itasca.Runtime.Spec.Simd.CompareInteger
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdEffects

/-!
Sections, each formerly its own module: ValueSlots, LaneRelation, InputValues.
-/

/-! ## ValueSlots -/

section

/-!
Vector/scalar source values represented by runtime slots.

Main declarations: `vector_bits_to_nat` and `ValuesAt.simd_scalar_result`. A direct consumer is `Interp.Simd.Execution.ConstValues`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem vector_bits_to_nat (words : List U64) (position : Nat) :
    (vectorBits words position).toNat =
      ((words[position]?).getD 0#u64).val + ((words[position+1]?).getD 0#u64).val * 2^64 := by
  let lo := (words[position]?).getD 0#u64
  let hi := (words[position+1]?).getD 0#u64
  have hlo : lo.val < 2^64 := by scalar_tac
  have hloWide : lo.val < 2^128 := by scalar_tac
  have hhiWide : hi.val < 2^128 := by scalar_tac
  have hshift : hi.val * 2^64 < 2^128 := by scalar_tac
  change (lo.bv.setWidth 128 ||| (hi.bv.setWidth 128 <<< 64)).toNat = lo.val + hi.val * 2^64
  simp only [BitVec.toNat_or,BitVec.toNat_shiftLeft,BitVec.toNat_setWidth,UScalar.bv_toNat]
  rw [Nat.mod_eq_of_lt hloWide,Nat.mod_eq_of_lt hhiWide,Nat.shiftLeft_eq,Nat.mod_eq_of_lt hshift]
  rw [Nat.or_comm,←Nat.shiftLeft_eq,←Nat.shiftLeft_add_eq_or_of_lt hlo,Nat.shiftLeft_eq]
  omega

theorem WordsAt.simd_vector {words : List U64} {position bits : Nat}
    (represented : WordsAt words position (Compiler.encodeValue (.VCONST .V128 (.mk_uN bits)))) :
    (simdInput words position 2#u32).val = bits := by
  change WordsAt words position [bits%2^64,bits/2^64] at represented
  obtain ⟨loBound,loValue⟩ := represented 0 (by simp)
  obtain ⟨hiBound,hiValue⟩ := represented 1 (by simp)
  simp only [Nat.add_zero,List.getElem!_cons_zero] at loBound loValue
  simp only [List.getElem!_cons_succ,List.getElem!_cons_zero] at hiValue
  change (vectorBits words position).toNat = bits
  rw [vector_bits_to_nat]
  have lo : ((words[position]?).getD 0#u64).val = bits%2^64 := by
    simpa only [List.getElem?_eq_getElem loBound,Option.getD_some,_root_.getElem!_pos words position loBound] using loValue
  have hi : ((words[position+1]?).getD 0#u64).val = bits/2^64 := by
    simpa only [List.getElem?_eq_getElem hiBound,Option.getD_some,_root_.getElem!_pos words (position+1) hiBound] using hiValue
  rw [lo,hi,Nat.mul_comm]
  exact Nat.mod_add_div bits (2^64)

theorem ValuesAt.simd_vector_result {words : List U64} {base : Nat} {front : List val}
    (represented : ValuesAt words base front) (value : U128)
    (capacity : base + Compiler.slots (front.map Compiler.valueType) + 2 ≤ words.length) :
    ValuesAt (simdResultSlots words (base+Compiler.slots (front.map Compiler.valueType)) 2#u32 value) base
      (front ++ [.VCONST .V128 (.mk_uN value.val)]) := by
  have written := represented.append_vector (UScalar.cast .U64 value)
    ⟨(value.bv >>> 64).setWidth 64⟩ capacity
  have bits : (UScalar.cast .U64 value).val + ((value.bv >>> 64).setWidth 64).toNat * 2^64 = value.val := by
    simp only [UScalar.cast_val_eq,UScalarTy.numBits,BitVec.toNat_setWidth,BitVec.toNat_ushiftRight,UScalar.bv_toNat]
    rw [Nat.shiftRight_eq_div_pow]
    have high : value.val / 2^64 < 2^64 := by scalar_tac
    rw [Nat.mod_eq_of_lt high,Nat.mul_comm]
    exact Nat.mod_add_div value.val (2^64)
  have decoded : Store.decodeWords .V128 (UScalar.cast .U64 value) ⟨(value.bv >>> 64).setWidth 64⟩ =
      .VCONST .V128 (.mk_uN value.val) := by
    change val.VCONST .V128 (.mk_uN ((UScalar.cast .U64 value).val + ((value.bv >>> 64).setWidth 64).toNat * 2^64)) = _
    rw [bits]
  simpa only [simdResultSlots,show (2#u32).val > 0 from by decide,↓reduceIte,decoded] using written

theorem WordsAt.simd_scalar {words : List U64} {position bits : Nat} (width : U32)
    (scalar : width ≠ 2#u32) (represented : WordsAt words position [bits]) :
    (simdInput words position width).val = bits := by
  obtain ⟨bound,value⟩ := represented 0 (by simp)
  simp only [Nat.add_zero,List.getElem!_cons_zero] at bound value
  have word : ((words[position]?).getD 0#u64).val = bits := by
    simpa only [List.getElem?_eq_getElem bound,Option.getD_some,_root_.getElem!_pos words position bound] using value
  simp only [simdInput,if_neg scalar,UScalar.cast_val_eq]
  rw [Nat.mod_eq_of_lt (by scalar_tac)]
  exact word

theorem ValuesAt.simd_scalar_result {words : List U64} {base : Nat} {front : List val}
    (represented : ValuesAt words base front) (ty : Itasca.wasm_types.ValueType) (value : U128)
    (scalar : ty ≠ .V128)
    (small : ty = .I32 ∨ ty = .F32 → (UScalar.cast .U64 value).val < 2^32)
    (capacity : base + Compiler.slots (front.map Compiler.valueType) < words.length) :
    ValuesAt (simdResultSlots words (base+Compiler.slots (front.map Compiler.valueType)) 1#u32 value) base
      (front ++ [Store.decodeWords ty (UScalar.cast .U64 value) 0#u64]) := by
  have written := represented.append_scalar ty (UScalar.cast .U64 value) 0#u64 scalar small capacity
  simpa only [simdResultSlots,show (1#u32).val > 0 from by decide,show (1#u32) ≠ 2#u32 from by decide,↓reduceIte] using written
end Itasca.Runtime.Interp

end

/-! ## LaneRelation -/

section

/-!
Source effects and result values of SIMD lane instructions.

Main declarations: `LaneSourceEffect` and `LaneEntrySound`. A direct consumer is `Interp.Simd.Lanes.LaneEntries`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Wasm2.Simd

def laneResult (op : LaneOperation) (bits : BitVec 128) : val :=
  Spec.Simd.valueOfBits (if op.replace then .V128 else valtype_numtype op.scalar) bits

def LaneSourceEffect (op : LaneOperation) (laneIndex : Nat) (x y z value : BitVec 128) : Prop :=
  Step_pure ((Spec.Simd.operandValues op.inputs x y z).map admininstr_val ++
    [admininstr_instr (op.instruction (.mk_uN laneIndex))]) [admininstr_val (laneResult op value)]

def LaneResultBound (op : LaneOperation) (value : U128) : Prop :=
  op.replace = false → value.val < 2^(Spec.scalarNumBytes op.scalar*8)

def LaneEntrySound {F : Type} (floats : runtime.platform.FloatOps F) (opcode : U32) : Prop :=
  ∀ op : LaneOperation, laneMeaning opcode.val = some op →
    ∀ (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)),
    laneIndex.val < op.count →
    runtime.interp.simd.simd floats opcode offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧ LaneSourceEffect op laneIndex.val x.bv y.bv z.bv value.bv ∧ LaneResultBound op value ⦄

theorem extract_result_value (ty : lanetype) (value : U128) (bounded : value.val < 2^lsize ty) :
    admininstr_val (Spec.Simd.valueOfBits (valtype_numtype (unpack ty)) value.bv) =
      .CONST (unpack ty) (Spec.Simd.scalarOutput ty value.val) := by
  have narrow (n : Nat) (le : lsize ty ≤ n) : (value.bv.setWidth n).toNat = value.val := by
    rw [BitVec.toNat_setWidth,UScalar.bv_toNat,Nat.mod_eq_of_lt (lt_of_lt_of_le bounded (Nat.pow_le_pow_right (by decide) le))]
  cases ty <;> simp only [Spec.Simd.valueOfBits,Spec.Simd.scalarOutput,unpack,valtype_numtype,admininstr_val]
  all_goals rw [narrow _ (by decide)]

@[step] theorem extract_dispatch_values {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : lanetype) (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8))
    (valid : laneIndex.val < 128/lsize ty) :
    runtime.interp.simd.simd floats (extractOpcode ty) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),
          .VEXTRACT_LANE (Spec.Simd.shapeOf ty) (Spec.Simd.extractSign ty) (.mk_uN laneIndex.val)]
          [admininstr_val (Spec.Simd.valueOfBits (valtype_numtype (unpack ty)) value.bv)] ∧ value.val < 2^(Spec.scalarNumBytes (unpack ty)*8) ⦄ := by
  rw [extract_dispatch_eq]
  step with extract_access ty laneIndex x y valid as ⟨result,value,returned,valueEq⟩
  refine ⟨value,by rw [returned],?_,?_⟩
  · rw [extract_result_value ty value (by rw [valueEq];exact Nat.mod_lt _ (by positivity)),valueEq]
    exact Spec.Simd.extract_step ty laneIndex.val x.bv valid
  · rw [valueEq]
    exact lt_of_lt_of_le (Nat.mod_lt _ (by positivity))
      (Nat.pow_le_pow_right (by decide) (by cases ty <;> decide))
end Itasca.Runtime.Interp.Simd

end

/-! ## InputValues -/

section

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

end
