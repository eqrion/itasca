import Exec.Spec.SimdWiden
import Exec.Spec.SimdIntegerArithmetic
namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

def pairwiseHalfWords (ty : PairwiseWidth) (signed : Bool) (x : BitVec 128) (offset : Nat) : List uN :=
  (List.range ty.widen.count).map (fun j => .mk_uN
    (extendBits signed (ty.widen.width*2) (laneWord (lanetype_Jnn ty.widen.input) x (2*j+offset))).toNat)

def pairwiseWords (ty : PairwiseWidth) (signed : Bool) (x : BitVec 128) : List uN :=
  (List.range ty.widen.count).map (fun j => .mk_uN
    (pairwiseBits signed (laneWord (lanetype_Jnn ty.widen.input) x (2*j))
      (laneWord (lanetype_Jnn ty.widen.input) x (2*j+1))).toNat)

def pairwiseResult (ty : PairwiseWidth) (signed : Bool) (x : BitVec 128) : uN :=
  inv_lanes_ (shapeOf (lanetype_Jnn ty.widen.output)) (Map (lane_.mk_lane__0 ty.widen.output) (pairwiseWords ty signed x))

theorem pairwise_sum_relation (ty : PairwiseWidth) (signed : Bool) (x : BitVec 128) :
    Forall₃ (fun answer a b => fun_iadd_ (lsize (lanetype_Jnn ty.widen.output)) a b answer)
      (pairwiseWords ty signed x) (pairwiseHalfWords ty signed x 0) (pairwiseHalfWords ty signed x 1) := by
  apply forall3_map
  intro j member
  cases ty <;> exact integer_arithmetic_relation .add _ _

theorem pairwise_interleave (ty : PairwiseWidth) (signed : Bool) (x : BitVec 128) :
    concat_ uN (Map₂ (fun a b => [a,b]) (pairwiseHalfWords ty signed x 0) (pairwiseHalfWords ty signed x 1)) =
      Map (fun lane => extend__ ty.widen.width (lsize (lanetype_Jnn ty.widen.output)) (widenSign signed)
        (Option.get! (proj_lane__0 lane)))
        (lanes_ (shapeOf (lanetype_Jnn ty.widen.input)) (.mk_uN x.toNat)) := by
  rw [lanes_map_words]
  have allExtended : Map (fun lane => extend__ ty.widen.width (lsize (lanetype_Jnn ty.widen.output)) (widenSign signed)
      (Option.get! (proj_lane__0 lane)))
      ((List.range (128/ty.widen.width)).map (fun j => laneOfBits (lanetype_Jnn ty.widen.input) (laneWord (lanetype_Jnn ty.widen.input) x j).toNat)) =
      (List.range (128/ty.widen.width)).map (fun j => .mk_uN (extendBits signed (ty.widen.width*2)
        (laneWord (lanetype_Jnn ty.widen.input) x j)).toNat) := by
    simp only [Map,List.map_map]
    apply List.map_congr_left
    intro j member
    cases ty <;> exact (extend_bits_source _ signed _ (by decide)).symm
  apply Eq.trans (b := (List.range (128/ty.widen.width)).map (fun j => .mk_uN (extendBits signed (ty.widen.width*2) (laneWord (lanetype_Jnn ty.widen.input) x j)).toNat))
  · cases ty <;> rfl
  · exact allExtended.symm

theorem pairwise_words_wf (ty : PairwiseWidth) (signed : Bool) (x : BitVec 128) :
    Forall (fun word => wf_lane_ (lanetype_Jnn ty.widen.output) (.mk_lane__0 ty.widen.output word))
      (pairwiseWords ty signed x) := by
  intro word member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
  have wf := unsigned_wf_of_lt (ty.widen.width*2)
    (pairwiseBits signed (laneWord (lanetype_Jnn ty.widen.input) x (2*j))
      (laneWord (lanetype_Jnn ty.widen.input) x (2*j+1))).toNat (BitVec.isLt _)
  cases ty <;> exact .lane__case_0 _ _ _ wf rfl
end Itasca.Runtime.Spec.Simd
