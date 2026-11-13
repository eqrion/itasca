import SpecExt.Builtins.Examples
import Itasca.Runtime.Spec.SegmentInitCases
import Itasca.Runtime.Spec.Integer
import SpecExt.Builtins.Float.Sign

/-!
Sections, each formerly its own module: Bitwise, Shape, Replace, Extract, ExtractSigned, AnyTrue, ByteView, ByteSelect, Shuffle, Swizzle, PureValues, CompareInteger.
-/

/-! ## Bitwise -/

section

/-!
Source reduction for whole-vector bitwise operations.

Main declarations: `binary`. A direct consumer is `Spec.Simd.AnyTrue`.
-/

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

def binary (op : vvbinop) (a b : BitVec 128) : BitVec 128 :=
  match op with
  | .AND => a &&& b
  | .ANDNOT => a &&& ~~~b
  | .OR => a ||| b
  | .XOR => a ^^^ b

theorem not_value (a : BitVec 128) :
    vvunop_ .V128 .NOT (.mk_uN a.toNat) = .mk_uN (~~~a).toNat :=
  inot_bitvec a

theorem binary_value (op : vvbinop) (a b : BitVec 128) :
    vvbinop_ .V128 op (.mk_uN a.toNat) (.mk_uN b.toNat) =
      .mk_uN (binary op a b).toNat := by
  cases op
  · exact iand_bitvec a b
  · exact iandnot_bitvec a b
  · exact ior_bitvec a b
  · exact ixor_bitvec a b

theorem bitselect_value (a b c : BitVec 128) :
    vvternop_ .V128 .BITSELECT (.mk_uN a.toNat) (.mk_uN b.toNat) (.mk_uN c.toNat) =
      .mk_uN ((a &&& c) ||| (b &&& ~~~c)).toNat :=
  ibitselect_bitvec a b c

theorem const_wf (a : BitVec 128) :
    wf_admininstr (.VCONST .V128 (.mk_uN a.toNat)) := by
  apply wf_admininstr.admininstr_case_20 _ _ (by decide)
  exact unsigned_wf_of_lt 128 a.toNat (BitVec.toNat_lt_twoPow_of_le (by rfl))

theorem not_step (a : BitVec 128) :
    Step_pure [.VCONST .V128 (.mk_uN a.toNat), .VVUNOP .V128 .NOT]
      [.VCONST .V128 (.mk_uN (~~~a).toNat)] := by
  exact .vvunop _ _ _ (not_value a).symm (const_wf a)
    (.admininstr_case_21 ..) (const_wf _)

theorem binary_step (op : vvbinop) (a b : BitVec 128) :
    Step_pure [.VCONST .V128 (.mk_uN a.toNat), .VCONST .V128 (.mk_uN b.toNat),
      .VVBINOP .V128 op] [.VCONST .V128 (.mk_uN (binary op a b).toNat)] := by
  exact .vvbinop _ _ _ _ (binary_value op a b).symm (const_wf a) (const_wf b)
    (.admininstr_case_22 ..) (const_wf _)

theorem bitselect_step (a b c : BitVec 128) :
    Step_pure [.VCONST .V128 (.mk_uN a.toNat), .VCONST .V128 (.mk_uN b.toNat),
      .VCONST .V128 (.mk_uN c.toNat), .VVTERNOP .V128 .BITSELECT]
      [.VCONST .V128 (.mk_uN ((a &&& c) ||| (b &&& ~~~c)).toNat)] := by
  exact .vvternop _ _ _ _ _ (bitselect_value a b c).symm
    (const_wf a) (const_wf b) (const_wf c) (.admininstr_case_23 ..) (const_wf _)

end Itasca.Runtime.Spec.Simd

end

/-! ## Shape -/

section

/-!
Source lane shapes and scalar input types.

Main declarations: `shapeOf` and `scalarInput`. A direct consumer is `Spec.PureWf`.
-/

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

def shapeOf (ty : lanetype) : shape := .X ty (.mk_dim (128/lsize ty))

theorem shape_of_wf (ty : lanetype) : wf_shape (shapeOf ty) := by
  cases ty <;> constructor
  all_goals first | exact .dim_case_0 _ (by decide) | decide

theorem shape_of_covers (ty : lanetype) : lsize ty * (128/lsize ty) = 128 := by
  cases ty <;> decide

theorem lane_of_bits_wf (ty : lanetype) (bits : Nat) (bound : bits < 2^lsize ty) :
    wf_lane_ ty (laneOfBits ty bits) := by
  cases ty with
  | I8 => exact .lane__case_0 _ _ _ (unsigned_wf_of_lt 8 bits bound) rfl
  | I16 => exact .lane__case_0 _ _ _ (unsigned_wf_of_lt 16 bits bound) rfl
  | I32 => exact .lane__case_0 _ _ _ (unsigned_wf_of_lt 32 bits bound) rfl
  | I64 => exact .lane__case_0 _ _ _ (unsigned_wf_of_lt 64 bits bound) rfl
  | F32 => exact .lane__case_1 _ _ _ (floatOfBits_wf_32 bits bound) rfl
  | F64 => exact .lane__case_1 _ _ _ (floatOfBits_wf_64 bits bound) rfl

def scalarInput (ty : lanetype) (bits : BitVec 64) : num_ :=
  match ty with
  | .I8 | .I16 | .I32 => .mk_num__0 .I32 (.mk_uN (bits.setWidth 32).toNat)
  | .I64 => .mk_num__0 .I64 (.mk_uN bits.toNat)
  | .F32 => .mk_num__1 .F32 (floatOfBits 32 (bits.setWidth 32).toNat)
  | .F64 => .mk_num__1 .F64 (floatOfBits 64 bits.toNat)

theorem scalar_input_wf (ty : lanetype) (bits : BitVec 64) :
    wf_num_ (unpack ty) (scalarInput ty bits) := by
  cases ty with
  | I8 | I16 | I32 => exact unsigned_num_wf .I32 _ (BitVec.toNat_lt_twoPow_of_le (by rfl))
  | I64 => exact unsigned_num_wf .I64 _ (BitVec.toNat_lt_twoPow_of_le (by rfl))
  | F32 => exact float_num_wf .F32 _ (floatOfBits_wf_32 _ (BitVec.toNat_lt_twoPow_of_le (by rfl)))
  | F64 => exact float_num_wf .F64 _ (floatOfBits_wf_64 _ (BitVec.toNat_lt_twoPow_of_le (by rfl)))

theorem pack_scalar_input (ty : lanetype) (bits : BitVec 64) :
    fun_packnum_ ty (scalarInput ty bits)
      (some (laneOfBits ty (bits.setWidth (lsize ty)).toNat)) := by
  have wf := lane_of_bits_wf ty (bits.setWidth (lsize ty)).toNat
    (BitVec.toNat_lt_twoPow_of_le (by rfl))
  cases ty with
  | I32 => exact .fun_packnum__case_0 _ wf
  | I64 =>
    change fun_packnum_ .I64 _ (some (.mk_lane__0 .I64 (.mk_uN (bits.setWidth 64).toNat)))
    rw [BitVec.setWidth_eq]
    exact .fun_packnum__case_1 _ wf
  | F32 => exact .fun_packnum__case_2 _ wf
  | F64 =>
    change fun_packnum_ .F64 _ (some (.mk_lane__1 .F64 (floatOfBits 64 (bits.setWidth 64).toNat)))
    rw [BitVec.setWidth_eq]
    exact .fun_packnum__case_3 _ wf
  | I8 =>
    have truncated : wrap__ 32 8 (.mk_uN (bits.setWidth 32).toNat) =
        .mk_uN (bits.setWidth 8).toNat := by
      simp only [wrap__, BitVec.toNat_setWidth, proj_uN_0]
      congr 1
      exact Nat.mod_mod_of_dvd _ (by decide : 2^8 ∣ 2^32)
    have wf' : wf_lane_ .I8 (.mk_lane__0 .I8 (wrap__ 32 8 (.mk_uN (bits.setWidth 32).toNat))) := by
      rw [truncated]; exact wf
    have result := fun_packnum_.fun_packnum__case_4 (.mk_uN (bits.setWidth 32).toNat) (by decide) wf'
    change fun_packnum_ .I8 _ (some (.mk_lane__0 .I8 (wrap__ 32 8 (.mk_uN (bits.setWidth 32).toNat)))) at result
    rw [truncated] at result
    exact result
  | I16 =>
    have truncated : wrap__ 32 16 (.mk_uN (bits.setWidth 32).toNat) =
        .mk_uN (bits.setWidth 16).toNat := by
      simp only [wrap__, BitVec.toNat_setWidth, proj_uN_0]
      congr 1
      exact Nat.mod_mod_of_dvd _ (by decide : 2^16 ∣ 2^32)
    have wf' : wf_lane_ .I16 (.mk_lane__0 .I16 (wrap__ 32 16 (.mk_uN (bits.setWidth 32).toNat))) := by
      rw [truncated]; exact wf
    have result := fun_packnum_.fun_packnum__case_5 (.mk_uN (bits.setWidth 32).toNat) (by decide) wf'
    change fun_packnum_ .I16 _ (some (.mk_lane__0 .I16 (wrap__ 32 16 (.mk_uN (bits.setWidth 32).toNat)))) at result
    rw [truncated] at result
    exact result

theorem splat_step (ty : lanetype) (bits : BitVec 64) (result : BitVec 128)
    (packed : uN.mk_uN result.toNat = inv_lanes_ (shapeOf ty)
      (List.replicate (128/lsize ty) (laneOfBits ty (bits.setWidth (lsize ty)).toNat))) :
    Step_pure [.CONST (unpack ty) (scalarInput ty bits), .VSPLAT (shapeOf ty)]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  exact .vsplat ty (scalarInput ty bits) (128/lsize ty) (.mk_uN result.toNat)
    (some (laneOfBits ty (bits.setWidth (lsize ty)).toNat))
    (pack_scalar_input ty bits) (by simp) packed
    (.admininstr_case_13 _ _ (scalar_input_wf ty bits))
    (.admininstr_case_33 _ (shape_of_wf ty)) (const_wf result) (shape_of_wf ty)

end Itasca.Runtime.Spec.Simd

end

/-! ## Replace -/

section

/-!
Lane-index bounds and the source replacement step.

Main declarations: `index_wf` and `replace_step`. A direct consumer is `Spec.Simd.Extract`.
-/

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem index_wf (ty : lanetype) (index : Nat) (valid : index < 128/lsize ty) :
    wf_uN 8 (.mk_uN index) := by
  apply unsigned_wf_of_lt
  have bound : 128/lsize ty ≤ 16 := by cases ty <;> decide
  omega

theorem replace_step (ty : lanetype) (index : Nat) (before result : BitVec 128) (input : BitVec 64)
    (valid : index < 128/lsize ty)
    (packed : uN.mk_uN result.toNat = inv_lanes_ (shapeOf ty)
      ((lanes_ (shapeOf ty) (.mk_uN before.toNat)).set index
        (laneOfBits ty (input.setWidth (lsize ty)).toNat))) :
    Step_pure [.VCONST .V128 (.mk_uN before.toNat), .CONST (unpack ty) (scalarInput ty input),
      .VREPLACE_LANE (shapeOf ty) (.mk_uN index)] [.VCONST .V128 (.mk_uN result.toNat)] := by
  apply Step_pure.vreplace_lane _ ty (scalarInput ty input) (128/lsize ty) (.mk_uN index) _
    (some (laneOfBits ty (input.setWidth (lsize ty)).toNat))
  · exact pack_scalar_input ty input
  · simp
  · simpa only [List.modify_eq_set, proj_uN_0, Option.get!, shapeOf] using packed
  · exact const_wf before
  · exact .admininstr_case_13 _ _ (scalar_input_wf ty input)
  · exact .admininstr_case_35 _ _ (shape_of_wf ty) (index_wf ty index valid)
  · exact const_wf result
  · exact shape_of_wf ty

end Itasca.Runtime.Spec.Simd

end

/-! ## Extract -/

section

/-!
Scalar output types and signedness for lane extraction.

Main declarations: `scalarOutput` and `extractSign`. A direct consumer is `Spec.Simd.ByteView`.
-/

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

def scalarOutput (ty : lanetype) (bits : Nat) : num_ :=
  match ty with
  | .I8 | .I16 | .I32 => .mk_num__0 .I32 (.mk_uN bits)
  | .I64 => .mk_num__0 .I64 (.mk_uN bits)
  | .F32 => .mk_num__1 .F32 (floatOfBits 32 bits)
  | .F64 => .mk_num__1 .F64 (floatOfBits 64 bits)

theorem scalar_output_wf (ty : lanetype) (bits : Nat) (bound : bits < 2^lsize ty) :
    wf_num_ (unpack ty) (scalarOutput ty bits) := by
  cases ty with
  | I8 =>
    apply unsigned_num_wf .I32
    change bits < 2^8 at bound
    change bits < 2^32
    omega
  | I16 =>
    apply unsigned_num_wf .I32
    change bits < 2^16 at bound
    change bits < 2^32
    omega
  | I32 => exact unsigned_num_wf .I32 _ bound
  | I64 => exact unsigned_num_wf .I64 _ bound
  | F32 => exact float_num_wf .F32 _ (floatOfBits_wf_32 _ bound)
  | F64 => exact float_num_wf .F64 _ (floatOfBits_wf_64 _ bound)

theorem unpack_lane_of_bits (ty : lanetype) (bits : Nat) (bound : bits < 2^lsize ty) :
    fun_unpacknum_ ty (laneOfBits ty bits) (some (scalarOutput ty bits)) := by
  have wf := scalar_output_wf ty bits bound
  cases ty with
  | I32 => exact .fun_unpacknum__case_0 _ wf
  | I64 => exact .fun_unpacknum__case_1 _ wf
  | F32 => exact .fun_unpacknum__case_2 _ wf
  | F64 => exact .fun_unpacknum__case_3 _ wf
  | I8 => exact .fun_unpacknum__case_4 _ (by decide) wf
  | I16 => exact .fun_unpacknum__case_5 _ (by decide) wf

theorem lanes_get (ty : lanetype) (v : BitVec 128) (index : Nat)
    (valid : index < 128/lsize ty) :
    (lanes_ (shapeOf ty) (.mk_uN v.toNat))[index]! =
      laneOfBits ty (v.toNat/2^(lsize ty*index)%2^lsize ty) := by
  change (unpackLanes ty (128/lsize ty) v.toNat)[index]! = _
  rw [List.getElem!_eq_getElem?_getD, unpackLanes_getElem?, if_pos valid, Option.getD_some]

def extractSign (ty : lanetype) : Option sx :=
  match ty with
  | .I8 | .I16 => some .U
  | _ => none

theorem extract_wf (ty : lanetype) (index : Nat) (valid : index < 128/lsize ty) :
    wf_admininstr (.VEXTRACT_LANE (shapeOf ty) (extractSign ty) (.mk_uN index)) := by
  apply wf_admininstr.admininstr_case_34 _ _ _ (shape_of_wf ty) (index_wf ty index valid) (by decide)
  cases ty <;> decide

theorem extract_num_step (nt : numtype) (index : Nat) (v : BitVec 128)
    (valid : index < 128/lsize (lanetype_numtype nt)) :
    Step_pure [.VCONST .V128 (.mk_uN v.toNat),
      .VEXTRACT_LANE (shapeOf (lanetype_numtype nt)) none (.mk_uN index)]
      [.CONST nt (scalarOutput (lanetype_numtype nt)
        (v.toNat/2^(lsize (lanetype_numtype nt)*index)%2^lsize (lanetype_numtype nt)))] := by
  have wf := scalar_output_wf (lanetype_numtype nt)
    (v.toNat/2^(lsize (lanetype_numtype nt)*index)%2^lsize (lanetype_numtype nt))
    (Nat.mod_lt _ (by positivity))
  apply Step_pure.vextract_lane_num _ nt (128/lsize (lanetype_numtype nt)) (.mk_uN index) _
    (some (scalarOutput (lanetype_numtype nt)
      (v.toNat/2^(lsize (lanetype_numtype nt)*index)%2^lsize (lanetype_numtype nt))))
  · simpa only [lanes_, proj_uN_0, unpackLanes_length] using valid
  · change fun_unpacknum_ _ (lanes_ (shapeOf (lanetype_numtype nt)) (.mk_uN v.toNat))[index]! _
    rw [lanes_get _ _ _ valid]
    exact unpack_lane_of_bits _ _ (Nat.mod_lt _ (by positivity))
  · simp
  · rfl
  · exact const_wf v
  · have result := extract_wf (lanetype_numtype nt) index valid
    cases nt <;> exact result
  · apply wf_admininstr.admininstr_case_13
    cases nt <;> exact wf
  · exact shape_of_wf _

theorem extract_pack_step (pt : packtype) (index : Nat) (v : BitVec 128)
    (valid : index < 128/lsize (lanetype_packtype pt)) :
    Step_pure [.VCONST .V128 (.mk_uN v.toNat),
      .VEXTRACT_LANE (shapeOf (lanetype_packtype pt)) (some .U) (.mk_uN index)]
      [.CONST .I32 (scalarOutput (lanetype_packtype pt)
        (v.toNat/2^(lsize (lanetype_packtype pt)*index)%2^lsize (lanetype_packtype pt)))] := by
  have wf := scalar_output_wf (lanetype_packtype pt)
    (v.toNat/2^(lsize (lanetype_packtype pt)*index)%2^lsize (lanetype_packtype pt))
    (Nat.mod_lt _ (by positivity))
  apply Step_pure.vextract_lane_pack _ pt (128/lsize (lanetype_packtype pt)) .U (.mk_uN index)
  · cases pt <;> simp [scalarOutput, lanetype_packtype, proj_num__0]
  · change proj_lane__0 (lanes_ (shapeOf (lanetype_packtype pt)) (.mk_uN v.toNat))[index]! ≠ none
    rw [lanes_get _ _ _ valid]
    cases pt <;> simp [laneOfBits, lanetype_packtype, proj_lane__0]
  · simpa only [lanes_, proj_uN_0, unpackLanes_length] using valid
  · change _ = extend__ _ _ _ (Option.get! (proj_lane__0
      (lanes_ (shapeOf (lanetype_packtype pt)) (.mk_uN v.toNat))[index]!))
    rw [lanes_get _ _ _ valid]
    cases pt <;> rfl
  · cases pt <;> exact wf
  · exact const_wf v
  · have result := extract_wf (lanetype_packtype pt) index valid
    cases pt <;> exact result
  · apply wf_admininstr.admininstr_case_13
    cases pt <;> exact wf
  · exact shape_of_wf _

theorem extract_step (ty : lanetype) (index : Nat) (v : BitVec 128)
    (valid : index < 128/lsize ty) :
    Step_pure [.VCONST .V128 (.mk_uN v.toNat),
      .VEXTRACT_LANE (shapeOf ty) (extractSign ty) (.mk_uN index)]
      [.CONST (unpack ty) (scalarOutput ty (v.toNat/2^(lsize ty*index)%2^lsize ty))] := by
  cases ty with
  | I32 => exact extract_num_step .I32 index v valid
  | I64 => exact extract_num_step .I64 index v valid
  | F32 => exact extract_num_step .F32 index v valid
  | F64 => exact extract_num_step .F64 index v valid
  | I8 => exact extract_pack_step .I8 index v valid
  | I16 => exact extract_pack_step .I16 index v valid

end Itasca.Runtime.Spec.Simd

end

/-! ## ExtractSigned -/

section

/-!
Well-formed signed lanes and their extraction step.

Main declarations: `signed_lane_num_wf` and `extract_signed_step`. A direct consumer is `Interp.Simd.Integer.ExtractSigned`.
-/

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem signed_lane_num_wf (width bits : Nat) (bound : bits < 2^width) :
    wf_num_ .I32 (.mk_num__0 .I32 (extend__ width 32 .S (.mk_uN bits))) := by
  have eq := extend_signed_bitvec width 32 (BitVec.ofNat width bits)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] at eq
  rw [eq]
  exact unsigned_num_wf .I32 _ (BitVec.toNat_lt_twoPow_of_le (by rfl))

theorem extract_signed_wf (ty : packtype) (index : Nat) (valid : index < 128/psize ty) :
    wf_admininstr (.VEXTRACT_LANE (shapeOf (lanetype_packtype ty)) (some .S) (.mk_uN index)) := by
  apply wf_admininstr.admininstr_case_34 _ _ _ (shape_of_wf _) (index_wf (lanetype_packtype ty) index (by cases ty <;> exact valid)) (by decide)
  cases ty <;> decide

theorem extract_signed_step (ty : packtype) (index : Nat) (v : BitVec 128)
    (valid : index < 128/psize ty) :
    Step_pure [.VCONST .V128 (.mk_uN v.toNat),
      .VEXTRACT_LANE (shapeOf (lanetype_packtype ty)) (some .S) (.mk_uN index)]
      [.CONST .I32 (.mk_num__0 .I32
        (extend__ (psize ty) 32 .S (.mk_uN (v.toNat/2^(psize ty*index)%2^psize ty))))] := by
  have sizes : lsize (lanetype_packtype ty) = psize ty := by cases ty <;> rfl
  have wf := signed_lane_num_wf (psize ty) (v.toNat/2^(psize ty*index)%2^psize ty)
    (Nat.mod_lt _ (by positivity))
  apply Step_pure.vextract_lane_pack _ ty (128/lsize (lanetype_packtype ty)) .S (.mk_uN index)
  · simp [proj_num__0]
  · change proj_lane__0 (lanes_ (shapeOf (lanetype_packtype ty)) (.mk_uN v.toNat))[index]! ≠ none
    rw [lanes_get _ _ _ (by simpa only [sizes] using valid)]
    cases ty <;> simp [laneOfBits, lanetype_packtype, proj_lane__0]
  · simpa only [lanes_, proj_uN_0, unpackLanes_length, sizes] using valid
  · change _ = extend__ _ _ _ (Option.get! (proj_lane__0
      (lanes_ (shapeOf (lanetype_packtype ty)) (.mk_uN v.toNat))[index]!))
    rw [lanes_get _ _ _ (by simpa only [sizes] using valid)]
    cases ty <;> rfl
  · exact wf
  · exact const_wf v
  · exact extract_signed_wf ty index valid
  · exact .admininstr_case_13 _ _ wf
  · exact shape_of_wf _

end Itasca.Runtime.Spec.Simd

end

/-! ## AnyTrue -/

section

/-!
The source relation and reduction step for any-true vector reduction.

Main declarations: `any_true_relation` and `any_true_step`. A direct consumer is `Interp.Simd.Bitwise.Whole`.
-/

namespace Itasca.Runtime.Spec.Simd

theorem any_true_relation (a : BitVec 128) :
    fun_ine_ 128 (.mk_uN a.toNat) (.mk_uN 0)
      (.mk_uN (if a.toNat ≠ 0 then 1 else 0)) := by
  have hbool : nat_of_bool (uN.mk_uN a.toNat != uN.mk_uN 0) =
      (if a.toNat ≠ 0 then 1 else 0) := by
    change nat_of_bool (a.toNat != 0) = _
    by_cases h : a.toNat = 0
    · simp [h, bne, nat_of_bool]
    · have hb : (a.toNat == 0) = false := beq_eq_false_iff_ne.mpr h
      simp [bne, hb, h, nat_of_bool]
  rw [←hbool]
  exact .fun_ine__case_0 _ _ _ (boolean_u32_wf _)

theorem any_true_step (a : BitVec 128) :
    Step_pure [.VCONST .V128 (.mk_uN a.toNat), .VVTESTOP .V128 .ANY_TRUE]
      [.CONST .I32 (.mk_num__0 .I32 (.mk_uN (if a.toNat ≠ 0 then 1 else 0)))] := by
  exact .vvtestop _ _ _ (by decide) (any_true_relation a) (by simp [proj_num__0]) rfl
    (predicate_i32_wf _) (const_wf a) (.admininstr_case_24 ..)
    (.admininstr_case_13 _ _ (predicate_i32_wf _))
    (unsigned_wf_of_lt 128 0 (by decide))

end Itasca.Runtime.Spec.Simd

end

/-! ## ByteView -/

section

/-!
A byte-indexed view of source vectors.

Main declarations: `byteAt` and `byteWords`. A direct consumer is `Spec.Simd.ByteSelect`.
-/

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

def byteAt (bits : BitVec 128) (index : Nat) : Nat := bits.toNat/2^(8*index)%2^8

def byteWords (bits : BitVec 128) : List uN := (List.range 16).map (fun i => .mk_uN (byteAt bits i))

theorem byte_at_bound (bits : BitVec 128) (index : Nat) : byteAt bits index < 2^8 :=
  Nat.mod_lt _ (by decide)

@[simp] theorem byte_words_length (bits : BitVec 128) : (byteWords bits).length = 16 := by
  simp [byteWords]

theorem byte_words_get (bits : BitVec 128) (index : Nat) (valid : index < 16) :
    (byteWords bits)[index]! = .mk_uN (byteAt bits index) := by
  simp [byteWords,List.getElem!_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,valid]

theorem byte_words_lanes (bits : BitVec 128) :
    (byteWords bits).map (lane_.mk_lane__0 .I8) = lanes_ (shapeOf .I8) (.mk_uN bits.toNat) := by
  apply List.ext_getElem?
  intro i
  change (((List.range 16).map (fun j => uN.mk_uN (byteAt bits j))).map (lane_.mk_lane__0 .I8))[i]? =
    (unpackLanes .I8 16 bits.toNat)[i]?
  rw [unpackLanes_getElem?]
  by_cases valid : i < 16
  · simp [List.getElem?_map,List.getElem?_range,valid,byteAt,lsize,psize,size,laneOfBits]
  · simp [List.getElem?_map,List.getElem?_range,valid]

theorem byte_words_wf (bits : BitVec 128) :
    Forall (fun word => wf_lane_ .I8 (.mk_lane__0 .I8 word)) (byteWords bits) := by
  intro word member
  obtain ⟨index,_,rfl⟩ := List.mem_map.mp member
  exact .lane__case_0 _ _ _ (unsigned_wf_of_lt 8 _ (byte_at_bound bits index)) rfl

end Itasca.Runtime.Spec.Simd

end

/-! ## ByteSelect -/

section

/-!
Byte-lane selection and list-index transport.

Main declarations: `byte_lanes_integer` and `byte_words_append_get`. A direct consumer is `Spec.Simd.Swizzle`.
-/

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem byte_lanes_integer (bits : BitVec 128) :
    Forall (fun lane => proj_lane__0 lane ≠ none) (lanes_ (shapeOf .I8) (.mk_uN bits.toNat)) := by
  rw [←byte_words_lanes]
  intro lane member
  obtain ⟨word,_,rfl⟩ := List.mem_map.mp member
  simp [proj_lane__0]

theorem byte_lanes_unwrap (bits : BitVec 128) :
    Map (fun lane => Option.get! (proj_lane__0 lane))
      (lanes_ (shapeOf .I8) (.mk_uN bits.toNat)) = byteWords bits := by
  rw [←byte_words_lanes]
  simp [Map,List.map_map,Function.comp_def,proj_lane__0]

theorem byte_lanes_get (bits : BitVec 128) (index : Nat) (valid : index < 16) :
    (lanes_ (shapeOf .I8) (.mk_uN bits.toNat))[index]! =
      .mk_lane__0 .I8 (.mk_uN (byteAt bits index)) := by
  exact lanes_get .I8 bits index valid

theorem byte_words_append_get (x y : BitVec 128) (index : Nat) (valid : index < 32) :
    (byteWords x ++ byteWords y)[index]! =
      if index < 16 then .mk_uN (byteAt x index) else .mk_uN (byteAt y (index-16)) := by
  by_cases first : index < 16
  · simp only [if_pos first]
    simp [List.getElem!_eq_getElem?_getD,List.getElem?_append,byteWords,first]
  · simp only [if_neg first]
    simp [List.getElem!_eq_getElem?_getD,List.getElem?_append,byteWords,first,show index-16 < 16 by omega]

end Itasca.Runtime.Spec.Simd

end

/-! ## Shuffle -/

section

/-!
The byte shape used by source shuffle operations.

Main declarations: `byteShape`. A direct consumer is `Spec.Simd.Swizzle`.
-/

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

def byteShape : ishape := .mk_ishape (shapeOf .I8)

theorem byte_shape_wf : wf_ishape byteShape :=
  .ishape_case_0 .I8 _ (shape_of_wf .I8) rfl

theorem shuffle_step (x y result : BitVec 128) (indices : List laneidx)
    (lengthEq : indices.length = 16)
    (bounded : ∀ index ∈ indices, proj_uN_0 index < 32)
    (packed : uN.mk_uN result.toNat = inv_lanes_ (shapeOf .I8)
      ((List.range 16).map (fun k => lane_.mk_lane__0 .I8
        ((byteWords x ++ byteWords y)[proj_uN_0 indices[k]!]!)))) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat), .VCONST .V128 (.mk_uN y.toNat),
      .VSHUFFLE byteShape indices] [.VCONST .V128 (.mk_uN result.toNat)] := by
  have indexBound (k : Nat) (hk : k < 16) : proj_uN_0 indices[k]! < 32 := by
    apply bounded
    rw [_root_.getElem!_pos indices k (by omega)]
    exact List.getElem_mem _
  have wordsWf : Forall (fun word => wf_lane_ .I8 (.mk_lane__0 .I8 word)) (byteWords x ++ byteWords y) := by
    intro word member
    rcases List.mem_append.mp member with left | right
    · exact byte_words_wf x word left
    · exact byte_words_wf y word right
  apply Step_pure.vshuffle (.mk_uN x.toNat) (.mk_uN y.toNat) .I8 16 indices
    (.mk_uN result.toNat) (byteWords x ++ byteWords y) 0
  · change (byteWords x ++ byteWords y).map (lane_.mk_lane__0 .I8) = _
    rw [List.map_append,byte_words_lanes,byte_words_lanes]
    rfl
  · intro k member
    simpa using indexBound k (List.mem_range.mp member)
  · intro k member
    simpa [lengthEq] using List.mem_range.mp member
  · exact packed
  · exact const_wf x
  · exact const_wf y
  · apply wf_admininstr.admininstr_case_32 _ _ byte_shape_wf
    · intro index member
      have bound := bounded index member
      cases index with
      | mk_uN n =>
        exact unsigned_wf_of_lt 8 n (by change n < 32 at bound; omega)
    · exact ⟨rfl,lengthEq⟩
  · exact const_wf result
  · exact wordsWf
  · exact shape_of_wf .I8
  · intro k member
    apply wordsWf
    have bound : proj_uN_0 indices[k]! < (byteWords x ++ byteWords y).length := by
      simpa using indexBound k (List.mem_range.mp member)
    rw [_root_.getElem!_pos (byteWords x ++ byteWords y) (proj_uN_0 indices[k]!) bound]
    exact List.getElem_mem _

end Itasca.Runtime.Spec.Simd

end

/-! ## Swizzle -/

section

/-!
The source lane-word interpretation of swizzle.

Main declarations: `swizzleWords`. A direct consumer is `Interp.Simd.Lanes.Swizzle`.
-/

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins
set_option maxRecDepth 4096

def swizzleWords (bits : BitVec 128) : List uN := byteWords bits ++ List.replicate 240 (.mk_uN 0)

@[simp] theorem swizzle_words_length (bits : BitVec 128) : (swizzleWords bits).length = 256 := by
  simp only [swizzleWords,List.length_append,byte_words_length,List.length_replicate]

theorem swizzle_words_wf (bits : BitVec 128) :
    Forall (fun word => wf_lane_ .I8 (.mk_lane__0 .I8 word)) (swizzleWords bits) := by
  intro word member
  rcases List.mem_append.mp member with left | right
  · exact byte_words_wf bits word left
  · obtain ⟨_,rfl⟩ := List.mem_replicate.mp right
    exact .lane__case_0 _ _ _ (unsigned_wf_of_lt 8 0 (by decide)) rfl

theorem byte_lane_index (bits : BitVec 128) (index : Nat) (valid : index < 16) :
    proj_uN_0 (Option.get! (proj_lane__0 ((lanes_ (shapeOf .I8) (.mk_uN bits.toNat))[index]!))) =
      byteAt bits index := by
  rw [byte_lanes_get bits index valid]
  rfl

theorem swizzle_step (x y result : BitVec 128)
    (packed : uN.mk_uN result.toNat = inv_lanes_ (shapeOf .I8)
      ((List.range 16).map (fun k => lane_.mk_lane__0 .I8 ((swizzleWords x)[byteAt y k]!)))) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),.VCONST .V128 (.mk_uN y.toNat),.VSWIZZLE byteShape]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  apply Step_pure.vswizzle (.mk_uN x.toNat) (.mk_uN y.toNat) .I8 16 (.mk_uN result.toNat)
    (lanes_ (shapeOf .I8) (.mk_uN y.toNat)) (swizzleWords x) 0
  · rfl
  · exact byte_lanes_integer x
  · change swizzleWords x = Map (fun lane => Option.get! (proj_lane__0 lane))
      (lanes_ (shapeOf .I8) (.mk_uN x.toNat)) ++ List.replicate 240 (.mk_uN 0)
    rw [byte_lanes_unwrap]
    rfl
  · intro k member
    rw [byte_lane_index y k (List.mem_range.mp member),swizzle_words_length]
    exact byte_at_bound y k
  · intro k member
    rw [byte_lanes_get y k (List.mem_range.mp member)]
    simp [proj_lane__0]
  · intro k member
    simpa [lanes_,shapeOf,unpackLanes_length,lsize,psize] using List.mem_range.mp member
  · rw [packed]
    congr 1
    apply List.map_congr_left
    intro k member
    rw [byte_lane_index y k (List.mem_range.mp member)]
    rfl
  · exact const_wf x
  · exact const_wf y
  · exact .admininstr_case_31 _ byte_shape_wf rfl
  · exact const_wf result
  · exact shape_of_wf .I8
  · exact unsigned_wf_of_lt 8 0 (by decide)
  · intro k member
    rw [byte_lane_index y k (List.mem_range.mp member)]
    apply swizzle_words_wf
    have valid : byteAt y k < (swizzleWords x).length := by simpa using byte_at_bound y k
    rw [_root_.getElem!_pos (swizzleWords x) (byteAt y k) valid]
    exact List.getElem_mem _

end Itasca.Runtime.Spec.Simd

namespace Itasca.Runtime.Spec.Simd

theorem swizzle_words_get (bits : BitVec 128) (index : Nat) (valid : index < 256) :
    (swizzleWords bits)[index]! = if index < 16 then .mk_uN (byteAt bits index) else .mk_uN 0 := by
  simp only [swizzleWords,List.getElem!_eq_getElem?_getD,List.getElem?_append,byte_words_length]
  by_cases first : index < 16
  · simpa only [if_pos first,List.getElem!_eq_getElem?_getD] using byte_words_get bits index first
  · simp only [if_neg first,List.getElem?_replicate,if_pos (show index-16 < 240 by omega),Option.getD_some]

end Itasca.Runtime.Spec.Simd

end

/-! ## PureValues -/

section

/-!
Source values represented by SIMD operand bits. SIMD uses only numerical and vector types; reference cases retain a total definition.

Main declarations: `valueOfBits` and `operandValues`. A direct consumer is `Interp.Simd.Memory.Relation`.
-/

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

/-- Source values represented by SIMD operand bits. SIMD uses only numerical
and vector types; reference cases retain a total definition. -/
def valueOfBits (ty : valtype) (bits : BitVec 128) : val :=
  match ty with
  | .I32 => .CONST .I32 (.mk_num__0 .I32 (.mk_uN (bits.setWidth 32).toNat))
  | .I64 => .CONST .I64 (.mk_num__0 .I64 (.mk_uN (bits.setWidth 64).toNat))
  | .F32 => .CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (bits.setWidth 32).toNat))
  | .F64 => .CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 (bits.setWidth 64).toNat))
  | .V128 => .VCONST .V128 (.mk_uN bits.toNat)
  | .FUNCREF => .REF_NULL .FUNCREF
  | .EXTERNREF => .REF_NULL .EXTERNREF
  | .BOT => .REF_NULL .FUNCREF

/-- Up to three SIMD operands in their source order. -/
def operandValues (types : List valtype) (x y z : BitVec 128) : List val :=
  List.zipWith valueOfBits types [x,y,z]

end Itasca.Runtime.Spec.Simd

end

/-! ## CompareInteger -/

section

/-!
Integer SIMD comparison: scalar predicates, lane masks and source reduction. Floating-point comparisons reuse the lane-mask lemmas; runtime proofs consume the source-step result.
-/

/-! ## Simd Compare Integer -/

section

namespace Itasca.Runtime.Spec.Simd

def integerLaneCompare {width : Nat} (op : vrelop_Jnn_N) (a b : BitVec width) : Bool :=
  match op with
  | .EQ => decide (a.toNat = b.toNat)
  | .NE => decide (a.toNat ≠ b.toNat)
  | .LT .U => decide (a.toNat < b.toNat)
  | .GT .U => decide (a.toNat > b.toNat)
  | .LE .U => decide (a.toNat ≤ b.toNat)
  | .GE .U => decide (a.toNat ≥ b.toNat)
  | .LT .S => decide (a.toInt < b.toInt)
  | .GT .S => decide (a.toInt > b.toInt)
  | .LE .S => decide (a.toInt ≤ b.toInt)
  | .GE .S => decide (a.toInt ≥ b.toInt)

def IntegerLaneRel (op : vrelop_Jnn_N) (width : Nat) (a b answer : uN) : Prop :=
  match op with
  | .EQ => fun_ieq_ width a b answer
  | .NE => fun_ine_ width a b answer
  | .LT sign => fun_ilt_ width sign a b answer
  | .GT sign => fun_igt_ width sign a b answer
  | .LE sign => fun_ile_ width sign a b answer
  | .GE sign => fun_ige_ width sign a b answer

theorem integer_lane_compare_relation {width : Nat} (op : vrelop_Jnn_N) (a b : BitVec width) :
    IntegerLaneRel op width (.mk_uN a.toNat) (.mk_uN b.toNat)
      (.mk_uN (nat_of_bool (integerLaneCompare op a b))) := by
  cases op with
  | EQ => exact .fun_ieq__case_0 _ _ _ (boolean_u32_wf _)
  | NE =>
    have boolean : (uN.mk_uN a.toNat != uN.mk_uN b.toNat) = decide (a.toNat ≠ b.toNat) := by
      change (a.toNat != b.toNat) = _
      by_cases same : a.toNat = b.toNat
      · simp [same]
      · have different := beq_eq_false_iff_ne.mpr same
        simp [bne,different,same]
    have relation := fun_ine_.fun_ine__case_0 width (.mk_uN a.toNat) (.mk_uN b.toNat) (boolean_u32_wf _)
    rw [boolean] at relation
    exact relation
  | LT sign => cases sign with
    | U => exact .fun_ilt__case_0 _ _ _ (boolean_u32_wf _)
    | S => exact .fun_ilt__case_1 _ _ _ _ _ (bitvec_signed _ b) (bitvec_signed _ a) (boolean_u32_wf _)
  | GT sign => cases sign with
    | U => exact .fun_igt__case_0 _ _ _ (boolean_u32_wf _)
    | S => exact .fun_igt__case_1 _ _ _ _ _ (bitvec_signed _ b) (bitvec_signed _ a) (boolean_u32_wf _)
  | LE sign => cases sign with
    | U => exact .fun_ile__case_0 _ _ _ (boolean_u32_wf _)
    | S => exact .fun_ile__case_1 _ _ _ _ _ (bitvec_signed _ b) (bitvec_signed _ a) (boolean_u32_wf _)
  | GE sign => cases sign with
    | U => exact .fun_ige__case_0 _ _ _ (boolean_u32_wf _)
    | S => exact .fun_ige__case_1 _ _ _ _ _ (bitvec_signed _ b) (bitvec_signed _ a) (boolean_u32_wf _)

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Compare Shape -/

section

namespace Itasca.Runtime.Spec.Simd

def integerCompareSupported (ty : Jnn) (op : vrelop_Jnn_N) : Prop :=
  match ty,op with
  | .I64,.LT .U | .I64,.GT .U | .I64,.LE .U | .I64,.GE .U => False
  | _,_ => True

def integerCompareSource (ty : Jnn) (op : vrelop_Jnn_N) : vrelop_ :=
  .mk_vrelop__0 ty (128/lsize (lanetype_Jnn ty)) op

theorem integer_compare_source_wf (ty : Jnn) (op : vrelop_Jnn_N)
    (supported : integerCompareSupported ty op) :
    wf_vrelop_ (shapeOf (lanetype_Jnn ty)) (integerCompareSource ty op) := by
  apply wf_vrelop_.vrelop__case_0 _ _ _ _ ?_ rfl
  cases op with
  | EQ => constructor
  | NE => constructor
  | LT sign | GT sign | LE sign | GE sign =>
    constructor
    cases ty <;> cases sign <;> simp_all [integerCompareSupported,lsizenn,lsize,size,psize,lanetype_Jnn,isize,valtype_numtype]

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Compare Lists -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem forall3_map {I A B C : Type} (items : List I) (f : I → A) (g : I → B) (h : I → C)
    (P : A → B → C → Prop) (each : ∀ i ∈ items, P (f i) (g i) (h i)) :
    Forall₃ P (items.map f) (items.map g) (items.map h) := by
  induction items with
  | nil => simp [Forall₃]
  | cons head tail ih =>
    have atHead := each head (by simp)
    have atTail := ih (by intro i member; exact each i (by simp [member]))
    simpa [Forall₃] using And.intro atHead atTail

def laneWord (ty : lanetype) (bits : BitVec 128) (j : Nat) : BitVec (lsize ty) :=
  (bits >>> (lsize ty*j)).setWidth (lsize ty)

theorem lanes_map_words (ty : lanetype) (bits : BitVec 128) :
    lanes_ (shapeOf ty) (.mk_uN bits.toNat) =
      (List.range (128/lsize ty)).map (fun j => laneOfBits ty (laneWord ty bits j).toNat) := by
  apply unpackLanes_eq_map
  intro j valid
  simp [proj_uN_0,laneWord,BitVec.toNat_setWidth,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]

def comparisonAnswers (ty : Jnn) (op : vrelop_Jnn_N) (x y : BitVec 128) : List uN :=
  (List.range (128/lsize (lanetype_Jnn ty))).map (fun j =>
    .mk_uN (nat_of_bool (integerLaneCompare op (laneWord (lanetype_Jnn ty) x j) (laneWord (lanetype_Jnn ty) y j))))

theorem integer_lanes_nonempty (ty : Jnn) (x : BitVec 128) :
    Forall (fun lane => proj_lane__0 lane ≠ none) (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN x.toNat)) := by
  rw [lanes_map_words]
  intro lane member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
  cases ty <;> simp [laneOfBits,lanetype_Jnn,proj_lane__0]

theorem comparison_answers_relation (ty : Jnn) (op : vrelop_Jnn_N) (x y : BitVec 128) :
    Forall₃ (fun answer a b => IntegerLaneRel op (lsize (lanetype_Jnn ty))
      (Option.get! (proj_lane__0 a)) (Option.get! (proj_lane__0 b)) answer)
      (comparisonAnswers ty op x y)
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN x.toNat))
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN y.toNat)) := by
  rw [lanes_map_words,lanes_map_words]
  apply forall3_map
  intro j member
  have relation := integer_lane_compare_relation op (laneWord (lanetype_Jnn ty) x j) (laneWord (lanetype_Jnn ty) y j)
  cases ty <;> exact relation

theorem comparison_answers_length (ty : Jnn) (op : vrelop_Jnn_N) (x y : BitVec 128) :
    (comparisonAnswers ty op x y).length = 128/lsize (lanetype_Jnn ty) := by
  simp [comparisonAnswers]

theorem comparison_answers_wf (ty : Jnn) (op : vrelop_Jnn_N) (x y : BitVec 128) :
    Forall (fun answer => wf_uN 1 (.mk_uN (proj_uN_0 answer))) (comparisonAnswers ty op x y) := by
  intro answer member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
  cases integerLaneCompare op (laneWord (lanetype_Jnn ty) x j) (laneWord (lanetype_Jnn ty) y j) <;>
    apply wf_uN.uN_case_0 <;> decide

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Compare Masks -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

def comparisonMasks (ty : Jnn) (op : vrelop_Jnn_N) (x y : BitVec 128) : List uN :=
  Map (fun answer => extend__ 1 (lsize (lanetype_Jnn ty)) .S (.mk_uN (proj_uN_0 answer)))
    (comparisonAnswers ty op x y)

theorem boolean_extend (width : Nat) (answer : Bool) :
    extend__ 1 width .S (.mk_uN (nat_of_bool answer)) =
      .mk_uN ((BitVec.ofNat 1 (nat_of_bool answer)).signExtend width).toNat := by
  have bounded : nat_of_bool answer < 2^1 := by cases answer <;> decide
  simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt bounded] using
    extend_signed_bitvec 1 width (BitVec.ofNat 1 (nat_of_bool answer))

theorem comparison_masks_wf (ty : Jnn) (op : vrelop_Jnn_N) (x y : BitVec 128) :
    Forall (fun mask => wf_lane_ (lanetype_Jnn ty) (.mk_lane__0 ty mask))
      (comparisonMasks ty op x y) := by
  intro mask member
  obtain ⟨answer,answerMember,rfl⟩ := List.mem_map.mp member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp answerMember
  change wf_lane_ _ (.mk_lane__0 ty (extend__ 1 _ .S (.mk_uN (nat_of_bool _))))
  rw [boolean_extend]
  cases ty <;> constructor
  all_goals first | rfl | exact unsigned_wf_of_lt _ _ (BitVec.isLt _)

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Compare Relation -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

def integerComparisonResult (ty : Jnn) (op : vrelop_Jnn_N) (x y : BitVec 128) : uN :=
  inv_lanes_ (shapeOf (lanetype_Jnn ty))
    (Map (lane_.mk_lane__0 ty) (comparisonMasks ty op x y))

theorem integer_comparison_relation (ty : Jnn) (op : vrelop_Jnn_N) (x y : BitVec 128) :
    fun_vrelop_ (shapeOf (lanetype_Jnn ty)) (integerCompareSource ty op)
      (.mk_uN x.toNat) (.mk_uN y.toNat) (some (integerComparisonResult ty op x y)) := by
  have lenX : (comparisonAnswers ty op x y).length =
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN x.toNat)).length := by
    rw [comparison_answers_length,lanes_map_words,List.length_map,List.length_range]
  have lenY : (comparisonAnswers ty op x y).length =
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN y.toNat)).length := by
    rw [comparison_answers_length,lanes_map_words,List.length_map,List.length_range]
  have nonX := integer_lanes_nonempty ty x
  have nonY := integer_lanes_nonempty ty y
  have relation := comparison_answers_relation ty op x y
  have maskWf := comparison_masks_wf ty op x y
  have answerWf := comparison_answers_wf ty op x y
  have shapeWf := shape_of_wf (lanetype_Jnn ty)
  cases ty <;> cases op
  all_goals first
    | apply fun_vrelop_.fun_vrelop__case_0 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_1 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_2 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_3 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_4 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_5 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_6 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_7 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_8 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_9 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_10 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_11 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_12 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_13 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_14 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_15 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_16 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_17 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_18 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_19 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_20 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_21 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_22 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
    | apply fun_vrelop_.fun_vrelop__case_23 (var_1_lst := comparisonAnswers _ _ x y) (var_0_lst := comparisonAnswers _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := comparisonMasks _ _ x y)
  all_goals first
    | rfl
    | exact lenX
    | exact lenY
    | exact nonX
    | exact nonY
    | exact shapeWf
    | exact answerWf
    | exact maskWf
    | exact relation

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Compare Step -/

section

namespace Itasca.Runtime.Spec.Simd

theorem integer_comparison_step (ty : Jnn) (op : vrelop_Jnn_N) (x y result : BitVec 128)
    (supported : integerCompareSupported ty op)
    (packed : uN.mk_uN result.toNat = integerComparisonResult ty op x y) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),.VCONST .V128 (.mk_uN y.toNat),
      .VRELOP (shapeOf (lanetype_Jnn ty)) (integerCompareSource ty op)]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  apply Step_pure.vrelop _ _ _ _ _ (some (.mk_uN result.toNat))
  · rw [packed]
    exact integer_comparison_relation ty op x y
  · simp
  · rfl
  · exact const_wf x
  · exact const_wf y
  · exact .admininstr_case_28 _ _ (shape_of_wf _) (integer_compare_source_wf ty op supported)
  · exact const_wf result

end Itasca.Runtime.Spec.Simd

end

end
