import Exec.Spec.SimdCompareFloatLists
import Exec.Spec.FloatConvert
import Exec.Spec.SimdChoices
namespace Exec.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

def convertIntegerCount (ty : Fnn) : Nat := 128/lsize (lanetype_Fnn ty)
def convertIntegerHalf : Fnn → Option half | .F32 => none | .F64 => some .LOW

def convertIntegerSource (ty : Fnn) (sign : sx) : vcvtop__ :=
  .mk_vcvtop___1 .I32 4 ty (convertIntegerCount ty) (.CONVERT (convertIntegerHalf ty) sign)

def convertIntegerLane (ty : Fnn) (sign : sx) (word : uN) : lane_ :=
  .mk_lane__1 ty (convert__ 32 (lsize (lanetype_Fnn ty)) sign word)

def convertIntegerWords (ty : Fnn) (sign : sx) (x : BitVec 128) : List lane_ :=
  (List.range (convertIntegerCount ty)).map (fun j => convertIntegerLane ty sign (.mk_uN (laneWord .I32 x j).toNat))

def convertIntegerResult (ty : Fnn) (sign : sx) (x : BitVec 128) : uN :=
  inv_lanes_ (shapeOf (lanetype_Fnn ty)) (convertIntegerWords ty sign x)

theorem convert_integer_lane_wf (ty : Fnn) (sign : sx) (word : uN) :
    wf_lane_ (lanetype_Fnn ty) (convertIntegerLane ty sign word) := by
  have wf : wf_fN (lsize (lanetype_Fnn ty)) (convert__ 32 (lsize (lanetype_Fnn ty)) sign word) :=
    round_wf _ (by cases ty <;> decide) _ _
  cases ty <;> exact .lane__case_1 _ _ _ wf rfl

theorem convert_integer_lane_relation (ty : Fnn) (sign : sx) (word : uN) :
    fun_lcvtop__ (shapeOf .I32) (shapeOf (lanetype_Fnn ty)) (convertIntegerSource ty sign)
      (.mk_lane__0 .I32 word) (some [convertIntegerLane ty sign word]) := by
  have wf := convert_integer_lane_wf ty sign word
  cases ty
  · exact .fun_lcvtop___case_16 _ _ _ _ _ _ _ _ rfl wf rfl rfl
  · exact .fun_lcvtop___case_20 _ _ _ _ _ _ _ _ rfl wf rfl rfl

theorem convert_integer_source_wf (ty : Fnn) (sign : sx) :
    wf_vcvtop__ (shapeOf .I32) (shapeOf (lanetype_Fnn ty)) (convertIntegerSource ty sign) := by
  apply wf_vcvtop__.vcvtop___case_1
  · apply wf_vcvtop__Jnn_1_M_1_Fnn_2_M_2.vcvtop__Jnn_1_M_1_Fnn_2_M_2_case_0
    cases ty <;> decide
  · rfl
  · rfl

theorem convert_integer_half (ty : Fnn) (sign : sx) :
    fun_halfop (shapeOf .I32) (shapeOf (lanetype_Fnn ty)) (convertIntegerSource ty sign) (some (convertIntegerHalf ty)) := by
  cases ty
  · exact .fun_halfop_case_16 _ _ _ _ _ _ rfl rfl
  · exact .fun_halfop_case_20 _ _ _ _ _ _ rfl rfl

theorem convert_integer_zero (ty : Fnn) (sign : sx) :
    fun_zeroop (shapeOf .I32) (shapeOf (lanetype_Fnn ty)) (convertIntegerSource ty sign) (some none) := by
  cases ty
  · exact .fun_zeroop_case_16 _ _ _ _ _ _ rfl rfl
  · exact .fun_zeroop_case_20 _ _ _ _ _ _ rfl rfl

end Exec.Spec.Simd
