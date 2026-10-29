import Itasca.Runtime.Spec.Simd.FloatUnary
import Itasca.Runtime.Spec.FloatMinMax

/-!
Source-rule algebra for binary floating-point lanes. Lane/list calculations establish the generated source operation and its reduction step, consumed by source-machine and interpreter correspondence proofs.
-/

/-! ## Simd Float Binary -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

def floatBinaryChoices (width : Nat) (op : vbinop_Fnn_N) (a b : fN) : List fN :=
  match op with
  | .ADD => fadd_ width a b
  | .SUB => fsub_ width a b
  | .MUL => fmul_ width a b
  | .DIV => fdiv_ width a b
  | .MIN => fmin_ width a b
  | .MAX => fmax_ width a b
  | .PMIN => fpmin_ width a b
  | .PMAX => fpmax_ width a b

def floatBinarySource (ty : Fnn) (op : vbinop_Fnn_N) : vbinop_ :=
  .mk_vbinop__1 ty (128/lsize (lanetype_Fnn ty)) op

theorem float_binary_source_wf (ty : Fnn) (op : vbinop_Fnn_N) :
    wf_vbinop_ (shapeOf (lanetype_Fnn ty)) (floatBinarySource ty op) := by
  cases ty <;> cases op <;> constructor <;> constructor

theorem float_binary_choices_wf (width : Nat) (supported : width = 32 ∨ width = 64)
    (op : vbinop_Fnn_N) (a b : fN) (firstWf : wf_fN width a) (secondWf : wf_fN width b) :
    Forall (wf_fN width) (floatBinaryChoices width op a b) := by
  cases op with
  | ADD => exact add_wf width supported a b firstWf secondWf
  | SUB => exact sub_wf width supported a b firstWf secondWf
  | MUL => exact mul_wf width supported a b
  | DIV => exact div_wf width supported a b
  | MIN => exact float_min_wf width supported a b firstWf secondWf
  | MAX => exact float_max_wf width supported a b firstWf secondWf
  | PMIN =>
    intro result member
    simp only [floatBinaryChoices,fpmin_,List.mem_singleton] at member
    subst result
    split <;> assumption
  | PMAX =>
    intro result member
    simp only [floatBinaryChoices,fpmax_,List.mem_singleton] at member
    subst result
    split <;> assumption

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Float Binary Source -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

def floatBinaryLaneChoices (ty : Fnn) (op : vbinop_Fnn_N) (a b : lane_) : List lane_ :=
  Map (lane_.mk_lane__1 ty) (floatBinaryChoices (lsize (lanetype_Fnn ty)) op
    (Option.get! (proj_lane__1 a)) (Option.get! (proj_lane__1 b)))

def floatBinaryResults (ty : Fnn) (op : vbinop_Fnn_N) (x y : BitVec 128) : List uN :=
  Map (inv_lanes_ (shapeOf (lanetype_Fnn ty)))
    (setproduct_ lane_ (Map₂ (floatBinaryLaneChoices ty op)
      (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN x.toNat))
      (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN y.toNat))))

theorem float_binary_lanes_wf (ty : Fnn) (op : vbinop_Fnn_N) (x y : BitVec 128) :
    Forall₂ (fun a b => Forall (fun value => wf_lane_ (lanetype_Fnn ty) (.mk_lane__1 ty value))
      (floatBinaryChoices (lsize (lanetype_Fnn ty)) op
        (Option.get! (proj_lane__1 a)) (Option.get! (proj_lane__1 b))))
      (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN x.toNat))
      (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN y.toNat)) := by
  rw [lanes_map_words,lanes_map_words]
  apply forall2_map
  intro j member value allowed
  have wfInput (bits : BitVec 128) : wf_fN (lsize (lanetype_Fnn ty))
      (Option.get! (proj_lane__1 (laneOfBits (lanetype_Fnn ty) (laneWord (lanetype_Fnn ty) bits j).toNat))) := by
    cases ty <;> exact floatOfBits_wf _ (by decide) _
  have wf := float_binary_choices_wf (lsize (lanetype_Fnn ty)) (by cases ty <;> decide)
    op _ _ (wfInput x) (wfInput y) value allowed
  cases ty <;> exact .lane__case_1 _ _ _ wf rfl

theorem float_binary_relation (ty : Fnn) (op : vbinop_Fnn_N) (x y : BitVec 128) :
    fun_vbinop_ (shapeOf (lanetype_Fnn ty)) (floatBinarySource ty op)
      (.mk_uN x.toNat) (.mk_uN y.toNat) (some (floatBinaryResults ty op x y)) := by
  have shapeWf := shape_of_wf (lanetype_Fnn ty)
  have lanesWf := float_binary_lanes_wf ty op x y
  have lengths : (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN x.toNat)).length =
      (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN y.toNat)).length := by
    rw [lanes_map_words,lanes_map_words,List.length_map,List.length_map]
  cases ty <;> cases op
  · apply fun_vbinop_.fun_vbinop__case_36
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_38
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_40
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_42
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_44
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_46
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_48
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_50
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_37
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_39
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_41
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_43
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_45
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_47
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_49
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_51
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Float Binary Choices -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem float_binary_result_member (ty : Fnn) (op : vbinop_Fnn_N) (x y result : BitVec 128)
    (allowed : ∀ j, j < 128/lsize (lanetype_Fnn ty) →
      floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) result j).toNat ∈
        floatBinaryChoices (lsize (lanetype_Fnn ty)) op
          (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) x j).toNat)
          (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) y j).toNat)) :
    uN.mk_uN result.toNat ∈ floatBinaryResults ty op x y := by
  apply List.mem_map.mpr
  refine ⟨lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN result.toNat),?_,lanes_roundtrip _ result⟩
  rw [lanes_map_words,lanes_map_words,lanes_map_words]
  rw [map2_map]
  apply mem_setproduct_map
  intro j member
  have chosen := allowed j (List.mem_range.mp member)
  cases ty <;> exact List.mem_map.mpr ⟨_,chosen,rfl⟩

theorem float_binary_step (ty : Fnn) (op : vbinop_Fnn_N) (x y result : BitVec 128)
    (allowed : ∀ j, j < 128/lsize (lanetype_Fnn ty) →
      floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) result j).toNat ∈
        floatBinaryChoices (lsize (lanetype_Fnn ty)) op
          (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) x j).toNat)
          (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) y j).toNat)) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),.VCONST .V128 (.mk_uN y.toNat),
      .VBINOP (shapeOf (lanetype_Fnn ty)) (floatBinarySource ty op)] [.VCONST .V128 (.mk_uN result.toNat)] := by
  have chosen := float_binary_result_member ty op x y result allowed
  apply Step_pure.vbinop_val _ _ _ _ _ (some (floatBinaryResults ty op x y)) (float_binary_relation ty op x y)
  · exact List.length_pos_of_mem chosen
  · simp
  · simpa only [Option.get!_some,List.contains_iff_mem] using chosen
  · exact const_wf x
  · exact const_wf y
  · exact .admininstr_case_26 _ _ (shape_of_wf _) (float_binary_source_wf ty op)
  · exact const_wf result

end Itasca.Runtime.Spec.Simd

end
