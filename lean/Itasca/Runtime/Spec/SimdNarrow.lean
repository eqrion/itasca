import Itasca.Runtime.Spec.SimdQ15
namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem unsigned_saturate_bits (width : Nat) (x : Int) :
    uN.mk_uN (BitVec.ofInt width (clampLane width false x)).toNat = saturate width .U x := by
  rw [clamp_unsigned_toNat]
  have power : 0 < (2^width:Int) := pow_pos (by decide) _
  simp only [saturate,sat_u_,max_def,min_def]
  split_ifs <;> congr 1 <;> congr 1 <;> omega

def narrowBits (width : Nat) (signed : Bool) {input : Nat} (a : BitVec input) : BitVec width :=
  BitVec.ofInt width (clampLane width signed a.toInt)

theorem narrow_bits_source (width : Nat) (signed : Bool) {input : Nat} (a : BitVec input) :
    uN.mk_uN (narrowBits width signed a).toNat =
      narrow__ input width (if signed then .S else .U) (.mk_uN a.toNat) := by
  simp only [narrow__,proj_uN_0,Itasca.Runtime.Spec.signedValue_bitvec,narrowBits]
  cases signed
  · exact unsigned_saturate_bits width a.toInt
  · exact signed_saturate_bits width a.toInt

inductive NarrowWidth where | i8 | i16

def NarrowWidth.output : NarrowWidth → Jnn | .i8 => .I8 | .i16 => .I16

def NarrowWidth.input : NarrowWidth → Jnn | .i8 => .I16 | .i16 => .I32

def NarrowWidth.width (ty : NarrowWidth) : Nat := lsize (lanetype_Jnn ty.output)

def NarrowWidth.count (ty : NarrowWidth) : Nat := 128/lsize (lanetype_Jnn ty.input)

def narrowSource (ty : NarrowWidth) (signed : Bool) : admininstr :=
  .VNARROW (.mk_ishape (shapeOf (lanetype_Jnn ty.output)))
    (.mk_ishape (shapeOf (lanetype_Jnn ty.input))) (if signed then .S else .U)

theorem narrow_source_wf (ty : NarrowWidth) (signed : Bool) : wf_admininstr (narrowSource ty signed) := by
  have ishape (t : Jnn) : wf_ishape (.mk_ishape (shapeOf (lanetype_Jnn t))) :=
    .ishape_case_0 t _ (shapeOf_wf _) rfl
  cases ty <;> cases signed
  all_goals apply wf_admininstr.admininstr_case_38
  all_goals first | exact ishape _ | decide

def narrowWords (ty : NarrowWidth) (signed : Bool) (x : BitVec 128) : List uN :=
  (List.range ty.count).map (fun j => .mk_uN (narrowBits ty.width signed (laneWord (lanetype_Jnn ty.input) x j)).toNat)

def narrowResult (ty : NarrowWidth) (signed : Bool) (x y : BitVec 128) : uN :=
  inv_lanes_ (shapeOf (lanetype_Jnn ty.output))
    (Map (lane_.mk_lane__0 ty.output) (narrowWords ty signed x) ++ Map (lane_.mk_lane__0 ty.output) (narrowWords ty signed y))

end Itasca.Runtime.Spec.Simd
