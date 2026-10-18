import Exec.Spec.SimdCompareFloatLists
set_option maxHeartbeats 800000
namespace Exec.Spec.Simd
open SpecExt.Builtins

def averageBits {width : Nat} (a b : BitVec width) : BitVec width :=
  BitVec.ofNat width ((a.toNat+b.toNat+1)/2)

theorem average_bits_value {width : Nat} (a b : BitVec width) :
    (averageBits a b).toNat = (a.toNat+b.toNat+1)/2 := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [averageBits,BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]

def averageSupported (ty : Jnn) : Prop :=
  match ty with | .I8 | .I16 => True | _ => False

def averageSource (ty : Jnn) : vbinop_ :=
  .mk_vbinop__0 ty (128/lsize (lanetype_Jnn ty)) .AVGRU

theorem average_source_wf (ty : Jnn) (supported : averageSupported ty) :
    wf_vbinop_ (shapeOf (lanetype_Jnn ty)) (averageSource ty) := by
  cases ty <;> simp only [averageSupported] at supported
  all_goals try contradiction
  all_goals constructor <;> constructor
  all_goals decide

def averageWords (ty : Jnn) (x y : BitVec 128) : List uN :=
  (List.range (128/lsize (lanetype_Jnn ty))).map (fun j =>
    .mk_uN (averageBits (laneWord (lanetype_Jnn ty) x j) (laneWord (lanetype_Jnn ty) y j)).toNat)

def averageResult (ty : Jnn) (x y : BitVec 128) : uN :=
  inv_lanes_ (shapeOf (lanetype_Jnn ty)) (Map (lane_.mk_lane__0 ty) (averageWords ty x y))

theorem average_lanes_map (ty : Jnn) (x y : BitVec 128) :
    Map₂ (fun a b => lane_.mk_lane__0 ty (iavgr_ (lsize (lanetype_Jnn ty)) .U
      (Option.get! (proj_lane__0 a)) (Option.get! (proj_lane__0 b))))
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN x.toNat))
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN y.toNat)) =
        Map (lane_.mk_lane__0 ty) (averageWords ty x y) := by
  rw [lanes_map_words,lanes_map_words,map2_map]
  simp only [averageWords,Map,List.map_map]
  apply List.map_congr_left
  intro j member
  cases ty <;> simp only [laneOfBits,proj_lane__0,Option.get!,iavgr_,proj_uN_0,average_bits_value]
  all_goals rfl

theorem average_lanes_wf (ty : Jnn) (x y : BitVec 128) :
    Forall₂ (fun a b => wf_lane_ (lanetype_Jnn ty) (lane_.mk_lane__0 ty (iavgr_ (lsize (lanetype_Jnn ty)) .U
      (Option.get! (proj_lane__0 a)) (Option.get! (proj_lane__0 b)))))
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN x.toNat))
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN y.toNat)) := by
  rw [lanes_map_words,lanes_map_words]
  apply forall2_map
  intro j member
  have wf := unsigned_wf_of_lt (lsize (lanetype_Jnn ty))
    (averageBits (laneWord (lanetype_Jnn ty) x j) (laneWord (lanetype_Jnn ty) y j)).toNat (BitVec.isLt _)
  rw [average_bits_value] at wf
  cases ty <;> exact .lane__case_0 _ _ _ wf rfl

theorem average_vector_relation (ty : Jnn) (x y : BitVec 128) :
    fun_vbinop_ (shapeOf (lanetype_Jnn ty)) (averageSource ty)
      (.mk_uN x.toNat) (.mk_uN y.toNat) (some [averageResult ty x y]) := by
  have shapeWf := shapeOf_wf (lanetype_Jnn ty)
  have wf := average_lanes_wf ty x y
  have packed := congrArg (inv_lanes_ (shapeOf (lanetype_Jnn ty))) (average_lanes_map ty x y)
  have nonX := integer_lanes_nonempty ty x
  have nonY := integer_lanes_nonempty ty y
  have lengths : (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN x.toNat)).length =
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN y.toNat)).length := by
    rw [lanes_map_words,lanes_map_words,List.length_map,List.length_map]
  cases ty with
  | I32 => exact .fun_vbinop__case_28 _ _ _ _ _ _ _ rfl rfl nonX nonY packed.symm shapeWf lengths nonX nonY wf rfl
  | I64 => exact .fun_vbinop__case_29 _ _ _ _ _ _ _ rfl rfl nonX nonY packed.symm shapeWf lengths nonX nonY wf rfl
  | I8 => exact .fun_vbinop__case_30 _ _ _ _ _ _ _ rfl rfl nonX nonY packed.symm shapeWf lengths nonX nonY wf rfl
  | I16 => exact .fun_vbinop__case_31 _ _ _ _ _ _ _ rfl rfl nonX nonY packed.symm shapeWf lengths nonX nonY wf rfl

theorem average_step (ty : Jnn) (x y result : BitVec 128)
    (supported : averageSupported ty) (packed : uN.mk_uN result.toNat = averageResult ty x y) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),.VCONST .V128 (.mk_uN y.toNat),
      .VBINOP (shapeOf (lanetype_Jnn ty)) (averageSource ty)] [.VCONST .V128 (.mk_uN result.toNat)] := by
  apply Step_pure.vbinop_val _ _ _ _ _ (some [.mk_uN result.toNat])
  · rw [packed]; exact average_vector_relation ty x y
  · change 0 < 1; decide
  · simp
  · simp
  · exact const_wf x
  · exact const_wf y
  · exact .admininstr_case_26 _ _ (shapeOf_wf _) (average_source_wf ty supported)
  · exact const_wf result

end Exec.Spec.Simd
