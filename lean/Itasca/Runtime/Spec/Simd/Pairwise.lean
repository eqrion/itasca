import Itasca.Runtime.Spec.Simd.Widen
import Itasca.Runtime.Spec.Simd.IntegerArithmetic

/-!
Source-rule algebra for pairwise extended addition. Lane/list calculations establish the generated source operation and its reduction step, consumed by source-machine and interpreter correspondence proofs.
-/

/-! ## Simd Pairwise -/

section

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

end

/-! ## Simd Pairwise Source -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem pairwise_source_wf (ty : PairwiseWidth) (signed : Bool) : wf_admininstr (pairwiseSource ty signed) := by
  apply wf_admininstr.admininstr_case_36
  · exact .ishape_case_0 _ _ (shape_of_wf _) rfl
  · exact .ishape_case_0 _ _ (shape_of_wf _) rfl
  · apply wf_vextunop__.vextunop___case_0
    · apply wf_vextunop__Jnn_1_M_1_Jnn_2_M_2.vextunop__Jnn_1_M_1_Jnn_2_M_2_case_0
      cases ty <;> decide
    · rfl
    · cases ty <;> rfl

theorem pairwise_vector_relation (ty : PairwiseWidth) (signed : Bool) (x : BitVec 128) :
    fun_vextunop__ (.mk_ishape (shapeOf (lanetype_Jnn ty.widen.input)))
      (.mk_ishape (shapeOf (lanetype_Jnn ty.widen.output)))
      (.mk_vextunop___0 ty.widen.input (128/ty.widen.width) ty.widen.output ty.widen.count (.EXTADD_PAIRWISE (widenSign signed)))
      (.mk_uN x.toNat) (some (pairwiseResult ty signed x)) := by
  cases ty with
  | i8 =>
    apply fun_vextunop__.fun_vextunop___case_14 16 8 (widenSign signed) (.mk_uN x.toNat)
      (pairwiseHalfWords .i8 signed x 0) (pairwiseHalfWords .i8 signed x 1) 16 8
      (lanes_ (shapeOf .I8) (.mk_uN x.toNat)) (pairwiseResult .i8 signed x)
      (pairwiseWords .i8 signed x) (pairwiseWords .i8 signed x)
    · simp [pairwiseWords,pairwiseHalfWords]
    · simp [pairwiseWords,pairwiseHalfWords]
    · exact pairwise_sum_relation .i8 signed x
    · simp [pairwiseWords,pairwiseHalfWords]
    · simp [pairwiseWords,pairwiseHalfWords]
    · exact pairwise_sum_relation .i8 signed x
    · rfl
    · exact integer_lanes_nonempty .I8 x
    · exact pairwise_interleave .i8 signed x
    · rfl
    · exact shape_of_wf _
    · exact shape_of_wf _
    · exact pairwise_words_wf .i8 signed x
    · rfl
    · rfl
  | i16 =>
    apply fun_vextunop__.fun_vextunop___case_3 8 4 (widenSign signed) (.mk_uN x.toNat)
      (pairwiseHalfWords .i16 signed x 0) (pairwiseHalfWords .i16 signed x 1) 8 4
      (lanes_ (shapeOf .I16) (.mk_uN x.toNat)) (pairwiseResult .i16 signed x)
      (pairwiseWords .i16 signed x) (pairwiseWords .i16 signed x)
    · simp [pairwiseWords,pairwiseHalfWords]
    · simp [pairwiseWords,pairwiseHalfWords]
    · exact pairwise_sum_relation .i16 signed x
    · simp [pairwiseWords,pairwiseHalfWords]
    · simp [pairwiseWords,pairwiseHalfWords]
    · exact pairwise_sum_relation .i16 signed x
    · rfl
    · exact integer_lanes_nonempty .I16 x
    · exact pairwise_interleave .i16 signed x
    · rfl
    · exact shape_of_wf _
    · exact shape_of_wf _
    · exact pairwise_words_wf .i16 signed x
    · rfl
    · rfl

theorem pairwise_step (ty : PairwiseWidth) (signed : Bool) (x result : BitVec 128)
    (packed : uN.mk_uN result.toNat = pairwiseResult ty signed x) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),pairwiseSource ty signed]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  apply Step_pure.vextunop _ _ _ _ _ (some (.mk_uN result.toNat))
  · rw [packed]; exact pairwise_vector_relation ty signed x
  · simp
  · rfl
  · exact const_wf x
  · exact pairwise_source_wf ty signed
  · exact const_wf result
end Itasca.Runtime.Spec.Simd

end
