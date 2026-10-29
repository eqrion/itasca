import Itasca.Runtime.Spec.Simd.Q15

/-!
Source-rule algebra for narrowing lanes. Lane/list calculations establish the generated source operation and its reduction step, consumed by source-machine and interpreter correspondence proofs.
-/

/-! ## Simd Narrow -/

section

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

end

/-! ## Simd Narrow Source -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem narrow_lanes_map (ty : NarrowWidth) (signed : Bool) (x : BitVec 128) :
    Map (fun a => narrow__ (lsize (lanetype_Jnn ty.input)) ty.width (if signed then .S else .U)
      (Option.get! (proj_lane__0 a))) (lanes_ (shapeOf (lanetype_Jnn ty.input)) (.mk_uN x.toNat)) =
        narrowWords ty signed x := by
  rw [lanes_map_words]
  simp only [Map,List.map_map,narrowWords,NarrowWidth.count]
  apply List.map_congr_left
  intro j member
  cases ty <;> exact (narrow_bits_source _ signed (laneWord _ x j)).symm

theorem integer_lanes_wf (ty : Jnn) (x : BitVec 128) :
    Forall (wf_lane_ (lanetype_Jnn ty)) (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN x.toNat)) := by
  rw [lanes_map_words]
  intro lane member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
  have wf := unsigned_wf_of_lt (lsize (lanetype_Jnn ty)) (laneWord (lanetype_Jnn ty) x j).toNat (BitVec.isLt _)
  cases ty <;> exact .lane__case_0 _ _ _ wf rfl

theorem narrow_words_wf (ty : NarrowWidth) (signed : Bool) (x : BitVec 128) :
    Forall (fun word => wf_lane_ (lanetype_Jnn ty.output) (.mk_lane__0 ty.output word)) (narrowWords ty signed x) := by
  intro word member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
  have wf := unsigned_wf_of_lt ty.width (narrowBits ty.width signed (laneWord (lanetype_Jnn ty.input) x j)).toNat (BitVec.isLt _)
  cases ty <;> exact .lane__case_0 _ _ _ wf rfl

theorem narrow_step (ty : NarrowWidth) (signed : Bool) (x y result : BitVec 128)
    (packed : uN.mk_uN result.toNat = narrowResult ty signed x y) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),.VCONST .V128 (.mk_uN y.toNat),narrowSource ty signed]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  apply Step_pure.vnarrow (.mk_uN x.toNat) (.mk_uN y.toNat) ty.output _ ty.input _
    (if signed then .S else .U) (.mk_uN result.toNat)
    (lanes_ (shapeOf (lanetype_Jnn ty.input)) (.mk_uN x.toNat))
    (lanes_ (shapeOf (lanetype_Jnn ty.input)) (.mk_uN y.toNat))
    (narrowWords ty signed x) (narrowWords ty signed y)
  · rfl
  · rfl
  · exact integer_lanes_nonempty _ x
  · exact (narrow_lanes_map ty signed x).symm
  · exact integer_lanes_nonempty _ y
  · exact (narrow_lanes_map ty signed y).symm
  · exact packed
  · exact integer_lanes_wf _ x
  · exact integer_lanes_wf _ y
  · exact const_wf x
  · exact const_wf y
  · exact narrow_source_wf ty signed
  · exact const_wf result
  · exact shapeOf_wf _
  · exact shapeOf_wf _
  · exact narrow_words_wf ty signed x
  · exact narrow_words_wf ty signed y

end Itasca.Runtime.Spec.Simd

end
