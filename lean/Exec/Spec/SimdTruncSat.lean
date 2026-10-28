import Exec.Spec.FloatTrunc
import Exec.Spec.SimdCompareFloatLists
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
