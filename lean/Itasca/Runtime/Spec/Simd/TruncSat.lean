import Itasca.Runtime.Spec.FloatTrunc
import Itasca.Runtime.Spec.Simd.CompareFloat
import Itasca.Runtime.Spec.Simd.FloatUnary

/-!
Source-rule algebra for saturating float-to-integer lane conversion. Lane/list calculations establish the generated source operation and its reduction step, consumed by source-machine and interpreter correspondence proofs.
-/

/-! ## Simd Trunc Sat -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

def truncSatWord (source : Nat) (sign : sx) (value : fN) : uN :=
  Option.get! (trunc_sat__ source 32 sign value)

theorem trunc_sat_word_some (source : Nat) (sign : sx) (value : fN) :
    trunc_sat__ source 32 sign value = some (truncSatWord source sign value) := by
  unfold truncSatWord trunc_sat__
  split_ifs <;> rfl

theorem trunc_sat_word_wf (source : Nat) (sign : sx) (value : fN) :
    wf_uN 32 (truncSatWord source sign value) := by
  have wf := Itasca.Runtime.Spec.float_trunc_sat_results_wf source .I32 sign value
  change Forall (fun result => wf_num_ .I32 (.mk_num__0 .I32 result)) (trunc_sat__ source 32 sign value).toList at wf
  rw [trunc_sat_word_some] at wf
  have numeric := wf (truncSatWord source sign value) (by simp)
  cases numeric <;> assumption

theorem trunc_sat_word_bound (source : Nat) (sign : sx) (value : fN) :
    proj_uN_0 (truncSatWord source sign value) < 2^32 := by
  have all (word : uN) (wf : wf_uN 32 word) : proj_uN_0 word < 2^32 := by
    cases wf with
    | uN_case_0 n bound => norm_num [proj_uN_0] at bound ⊢; omega
  exact all _ (trunc_sat_word_wf source sign value)

end Itasca.Runtime.Spec.Simd
namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

def truncSatCount (ty : Fnn) : Nat := 128/lsize (lanetype_Fnn ty)
def truncSatZero : Fnn → Option zero | .F32 => none | .F64 => some .ZERO

def truncSatSource (ty : Fnn) (sign : sx) : vcvtop__ :=
  .mk_vcvtop___2 ty (truncSatCount ty) .I32 4 (.TRUNC_SAT sign (truncSatZero ty))

def truncSatLane (ty : Fnn) (sign : sx) (value : fN) : lane_ :=
  .mk_lane__0 .I32 (truncSatWord (lsize (lanetype_Fnn ty)) sign value)

def truncSatWords (ty : Fnn) (sign : sx) (x : BitVec 128) : List lane_ :=
  (List.range (truncSatCount ty)).map (fun j => truncSatLane ty sign
    (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) x j).toNat))

def truncSatResult (ty : Fnn) (sign : sx) (x : BitVec 128) : uN :=
  inv_lanes_ (shapeOf .I32) (truncSatWords ty sign x ++ List.replicate (4-truncSatCount ty) (.mk_lane__0 .I32 (.mk_uN 0)))

theorem trunc_sat_lane_relation (ty : Fnn) (sign : sx) (value : fN) :
    fun_lcvtop__ (shapeOf (lanetype_Fnn ty)) (shapeOf .I32) (truncSatSource ty sign)
      (.mk_lane__1 ty value) (some [truncSatLane ty sign value]) := by
  have eq := (trunc_sat_word_some (lsize (lanetype_Fnn ty)) sign value).symm
  have wf : Forall (fun word => wf_lane_ .I32 (.mk_lane__0 .I32 word))
      (some (truncSatWord (lsize (lanetype_Fnn ty)) sign value)).toList := by
    intro word member
    simp only [Option.toList_some,List.mem_singleton] at member
    subst word
    exact .lane__case_0 _ _ _ (trunc_sat_word_wf _ _ _) rfl
  cases ty
  · exact .fun_lcvtop___case_24 _ _ _ _ _ _ _ _ eq wf rfl rfl
  · exact .fun_lcvtop___case_25 _ _ _ _ _ _ _ _ eq wf rfl rfl

theorem trunc_sat_source_wf (ty : Fnn) (sign : sx) :
    wf_vcvtop__ (shapeOf (lanetype_Fnn ty)) (shapeOf .I32) (truncSatSource ty sign) := by
  apply wf_vcvtop__.vcvtop___case_2
  · apply wf_vcvtop__Fnn_1_M_1_Jnn_2_M_2.vcvtop__Fnn_1_M_1_Jnn_2_M_2_case_0
    cases ty <;> decide
  · rfl
  · rfl

theorem trunc_sat_half (ty : Fnn) (sign : sx) :
    fun_halfop (shapeOf (lanetype_Fnn ty)) (shapeOf .I32) (truncSatSource ty sign) (some none) := by
  cases ty
  · exact .fun_halfop_case_24 _ _ _ _ _ _ rfl rfl
  · exact .fun_halfop_case_25 _ _ _ _ _ _ rfl rfl

theorem trunc_sat_zero (ty : Fnn) (sign : sx) :
    fun_zeroop (shapeOf (lanetype_Fnn ty)) (shapeOf .I32) (truncSatSource ty sign) (some (truncSatZero ty)) := by
  cases ty
  · exact .fun_zeroop_case_24 _ _ _ _ _ _ rfl rfl
  · exact .fun_zeroop_case_25 _ _ _ _ _ _ rfl rfl

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Trunc Sat Source -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

def truncSatChoices (ty : Fnn) (sign : sx) (x : BitVec 128) : List (Option (List lane_)) :=
  (truncSatWords ty sign x).map (fun lane => some [lane])

theorem trunc_sat_lists_relation (ty : Fnn) (sign : sx) (x : BitVec 128) :
    Forall₂ (fun choices input => fun_lcvtop__ (shapeOf (lanetype_Fnn ty)) (shapeOf .I32) (truncSatSource ty sign) input choices)
      (truncSatChoices ty sign x) (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN x.toNat)) := by
  rw [lanes_map_words]
  unfold truncSatChoices truncSatWords
  rw [List.map_map]
  apply forall2_map
  intro j member
  cases ty <;> exact trunc_sat_lane_relation _ sign _

theorem trunc_sat_vector_relation (ty : Fnn) (sign : sx) (x result : BitVec 128)
    (packed : uN.mk_uN result.toNat = truncSatResult ty sign x) :
    fun_vcvtop__ (shapeOf (lanetype_Fnn ty)) (shapeOf .I32) (truncSatSource ty sign)
      (.mk_uN x.toNat) (some (.mk_uN result.toNat)) := by
  let choices := truncSatChoices ty sign x
  let inputs := lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN x.toNat)
  let outputs := truncSatWords ty sign x ++ List.replicate (4-truncSatCount ty) (.mk_lane__0 .I32 (.mk_uN 0))
  have nonempty : Forall (fun c => c ≠ none) choices := by
    intro c member
    obtain ⟨lane,_,rfl⟩ := List.mem_map.mp member
    simp
  have lengths : choices.length = inputs.length := by
    unfold choices inputs truncSatChoices truncSatWords truncSatCount
    rw [lanes_map_words]
    simp only [List.length_map]
  have member : (.mk_uN result.toNat) ∈ Map (inv_lanes_ (shapeOf .I32)) [outputs] := by
    rw [packed]
    exact List.mem_map.mpr ⟨outputs,List.mem_cons_self,rfl⟩
  have wf := unsigned_wf_of_lt 128 result.toNat result.isLt
  cases ty
  · apply fun_vcvtop__.fun_vcvtop___case_0 .F32 4 .I32 (truncSatSource .F32 sign)
      (.mk_uN x.toNat) (.mk_uN result.toNat) 4 inputs [outputs] choices (some none) (some none)
    · exact lengths
    · exact trunc_sat_lists_relation .F32 sign x
    · exact trunc_sat_zero .F32 sign
    · exact trunc_sat_half .F32 sign
    · simp
    · simp
    · exact ⟨rfl,rfl⟩
    · rfl
    · exact nonempty
    · rfl
    · exact List.length_pos_of_mem member
    · simpa only [List.contains_iff_mem,shapeOf,lsize,size,valtype_numtype,Option.get!_some] using member
    · exact wf
    · exact shapeOf_wf _
    · exact shapeOf_wf _
    · rfl
  · apply fun_vcvtop__.fun_vcvtop___case_2 .F64 2 .I32 4 (truncSatSource .F64 sign)
      (.mk_uN x.toNat) (.mk_uN result.toNat) inputs [outputs] (.mk_num__0 .I32 (.mk_uN 0))
      (some (.mk_lane__0 .I32 (.mk_uN 0))) choices (some (some .ZERO))
    · constructor; exact Itasca.Runtime.Spec.unsigned_num_wf .I32 0 (by decide)
    · constructor; exact .lane__case_0 _ _ _ (unsigned_wf_of_lt 32 0 (by decide)) rfl
    · exact lengths
    · exact trunc_sat_lists_relation .F64 sign x
    · exact trunc_sat_zero .F64 sign
    · simp
    · rfl
    · rfl
    · exact nonempty
    · simp
    · rfl
    · exact List.length_pos_of_mem member
    · simpa only [List.contains_iff_mem,shapeOf,lsize,size,valtype_numtype,Option.get!_some] using member
    · exact wf
    · exact shapeOf_wf _
    · exact shapeOf_wf _

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Trunc Sat Step -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem trunc_sat_packed (ty : Fnn) (sign : sx) (x result : BitVec 128)
    (allowed : ∀ j, j < truncSatCount ty →
      uN.mk_uN (laneWord .I32 result j).toNat = truncSatWord (lsize (lanetype_Fnn ty)) sign
        (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) x j).toNat))
    (zeroed : ∀ j, truncSatCount ty ≤ j → j < 4 → laneWord .I32 result j = 0) :
    uN.mk_uN result.toNat = truncSatResult ty sign x := by
  rw [←lanes_roundtrip .I32 result]
  apply congrArg (inv_lanes_ (shapeOf .I32))
  rw [lanes_map_words]
  change (List.range 4).map _ = _
  have mapped : (List.range 4).map (fun j => laneOfBits .I32 (laneWord .I32 result j).toNat) =
      (List.range 4).map (fun j => if j < truncSatCount ty then truncSatLane ty sign
        (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) x j).toNat)
        else .mk_lane__0 .I32 (.mk_uN 0)) := by
    apply List.map_congr_left
    intro j member
    by_cases valid : j < truncSatCount ty
    · rw [if_pos valid]
      exact congrArg (lane_.mk_lane__0 .I32) (allowed j valid)
    · rw [if_neg valid,zeroed j (by omega) (List.mem_range.mp member)]
      rfl
  rw [mapped]
  cases ty <;> rfl

theorem trunc_sat_step (ty : Fnn) (sign : sx) (x result : BitVec 128)
    (allowed : ∀ j, j < truncSatCount ty →
      uN.mk_uN (laneWord .I32 result j).toNat = truncSatWord (lsize (lanetype_Fnn ty)) sign
        (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) x j).toNat))
    (zeroed : ∀ j, truncSatCount ty ≤ j → j < 4 → laneWord .I32 result j = 0) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),
      .VCVTOP (shapeOf .I32) (shapeOf (lanetype_Fnn ty)) (truncSatSource ty sign)]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  have packed := trunc_sat_packed ty sign x result allowed zeroed
  apply Step_pure.vcvtop _ _ _ _ _ (some (.mk_uN result.toNat))
  · exact trunc_sat_vector_relation ty sign x result packed
  · simp
  · rfl
  · exact const_wf x
  · apply wf_admininstr.admininstr_case_39
    · exact shapeOf_wf _
    · exact shapeOf_wf _
    · exact trunc_sat_source_wf ty sign
  · exact const_wf result

end Itasca.Runtime.Spec.Simd

end
