import Exec.Spec.SimdQ15
import Exec.Spec.SimdCompareFloatLists
namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

def q15Source : vbinop_ := .mk_vbinop__0 .I16 8 .Q15MULR_SATS

theorem q15_source_wf : wf_vbinop_ (shapeOf .I16) q15Source := by
  constructor <;> constructor
  all_goals decide

def q15Words (x y : BitVec 128) : List uN :=
  (List.range 8).map (fun j => .mk_uN (q15Bits (laneWord .I16 x j) (laneWord .I16 y j)).toNat)

def q15Result (x y : BitVec 128) : uN :=
  inv_lanes_ (shapeOf .I16) (Map (lane_.mk_lane__0 .I16) (q15Words x y))

theorem q15_lanes_map (x y : BitVec 128) :
    Map₂ (fun a b => lane_.mk_lane__0 .I16 (iq15mulr_sat_ 16 .S
      (Option.get! (proj_lane__0 a)) (Option.get! (proj_lane__0 b))))
      (lanes_ (shapeOf .I16) (.mk_uN x.toNat)) (lanes_ (shapeOf .I16) (.mk_uN y.toNat)) =
        Map (lane_.mk_lane__0 .I16) (q15Words x y) := by
  rw [lanes_map_words,lanes_map_words,map2_map]
  simp only [q15Words,Map,List.map_map]
  apply List.map_congr_left
  intro j member
  exact congrArg (lane_.mk_lane__0 .I16) (q15_bits_source (laneWord .I16 x j) (laneWord .I16 y j)).symm

theorem q15_lanes_wf (x y : BitVec 128) :
    Forall₂ (fun a b => wf_lane_ .I16 (lane_.mk_lane__0 .I16 (iq15mulr_sat_ 16 .S
      (Option.get! (proj_lane__0 a)) (Option.get! (proj_lane__0 b)))))
      (lanes_ (shapeOf .I16) (.mk_uN x.toNat)) (lanes_ (shapeOf .I16) (.mk_uN y.toNat)) := by
  rw [lanes_map_words,lanes_map_words]
  apply forall2_map
  intro j member
  have wf := unsigned_wf_of_lt 16 (q15Bits (laneWord .I16 x j) (laneWord .I16 y j)).toNat (BitVec.isLt _)
  rw [q15_bits_source] at wf
  exact .lane__case_0 _ _ _ wf rfl

theorem q15_vector_relation (x y : BitVec 128) :
    fun_vbinop_ (shapeOf .I16) q15Source (.mk_uN x.toNat) (.mk_uN y.toNat) (some [q15Result x y]) := by
  have packed := congrArg (inv_lanes_ (shapeOf .I16)) (q15_lanes_map x y)
  have nonX := integer_lanes_nonempty .I16 x
  have nonY := integer_lanes_nonempty .I16 y
  have lengths : (lanes_ (shapeOf .I16) (.mk_uN x.toNat)).length =
      (lanes_ (shapeOf .I16) (.mk_uN y.toNat)).length := by
    rw [lanes_map_words,lanes_map_words,List.length_map,List.length_map]
  exact .fun_vbinop__case_35 _ _ _ _ _ _ _ rfl rfl nonX nonY packed.symm (shapeOf_wf _) lengths nonX nonY (q15_lanes_wf x y) rfl

theorem q15_step (x y result : BitVec 128) (packed : uN.mk_uN result.toNat = q15Result x y) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),.VCONST .V128 (.mk_uN y.toNat),
      .VBINOP (shapeOf .I16) q15Source] [.VCONST .V128 (.mk_uN result.toNat)] := by
  apply Step_pure.vbinop_val _ _ _ _ _ (some [.mk_uN result.toNat])
  · rw [packed]; exact q15_vector_relation x y
  · change 0 < 1; decide
  · simp
  · simp
  · exact const_wf x
  · exact const_wf y
  · exact .admininstr_case_26 _ _ (shapeOf_wf _) q15_source_wf
  · exact const_wf result

end Itasca.Runtime.Spec.Simd
