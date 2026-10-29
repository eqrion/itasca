import Itasca.Runtime.Spec.Simd.CompareFloat
import SpecExt.Builtins.Float.Wf
import Itasca.Runtime.Spec.Simd.Choices

/-!
Source-rule algebra for unary floating-point lanes. Lane/list calculations establish the generated source operation and its reduction step, consumed by source-machine and interpreter correspondence proofs.
-/

/-! ## Simd Float Unary -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

def floatUnaryChoices (width : Nat) (op : vunop_Fnn_N) (a : fN) : List fN :=
  match op with
  | .ABS => fabs_ width a
  | .NEG => fneg_ width a
  | .SQRT => fsqrt_ width a
  | .CEIL => fceil_ width a
  | .FLOOR => ffloor_ width a
  | .TRUNC => ftrunc_ width a
  | .NEAREST => fnearest_ width a

def floatUnarySource (ty : Fnn) (op : vunop_Fnn_N) : vunop_ :=
  .mk_vunop__1 ty (128/lsize (lanetype_Fnn ty)) op

theorem float_unary_source_wf (ty : Fnn) (op : vunop_Fnn_N) :
    wf_vunop_ (shapeOf (lanetype_Fnn ty)) (floatUnarySource ty op) := by
  cases ty <;> cases op <;> constructor <;> constructor

theorem float_unary_choices_wf (width : Nat) (supported : width = 32 ∨ width = 64)
    (op : vunop_Fnn_N) (a : fN) (inputWf : wf_fN width a) :
    Forall (wf_fN width) (floatUnaryChoices width op a) := by
  cases op with
  | ABS =>
    intro result member
    simp only [floatUnaryChoices,fabs_,List.mem_singleton] at member
    subst result
    exact withSign_wf (magnitude_wf inputWf) false
  | NEG =>
    intro result member
    simp only [floatUnaryChoices,fneg_,List.mem_singleton] at member
    subst result
    exact withSign_wf (magnitude_wf inputWf) _
  | SQRT => exact sqrt_wf width supported a inputWf
  | CEIL => exact integral_wf width supported _ a inputWf
  | FLOOR => exact integral_wf width supported _ a inputWf
  | TRUNC => exact integral_wf width supported _ a inputWf
  | NEAREST => exact integral_wf width supported _ a inputWf

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Float Unary Source -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

def floatUnaryLaneChoices (ty : Fnn) (op : vunop_Fnn_N) (lane : lane_) : List lane_ :=
  Map (lane_.mk_lane__1 ty) (floatUnaryChoices (lsize (lanetype_Fnn ty)) op (Option.get! (proj_lane__1 lane)))

def floatUnaryResults (ty : Fnn) (op : vunop_Fnn_N) (bits : BitVec 128) : List uN :=
  Map (inv_lanes_ (shapeOf (lanetype_Fnn ty)))
    (setproduct_ lane_ (Map (floatUnaryLaneChoices ty op)
      (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN bits.toNat))))

theorem float_unary_lanes_wf (ty : Fnn) (op : vunop_Fnn_N) (bits : BitVec 128) :
    Forall (fun lane => Forall (fun value => wf_lane_ (lanetype_Fnn ty) (.mk_lane__1 ty value))
      (floatUnaryChoices (lsize (lanetype_Fnn ty)) op (Option.get! (proj_lane__1 lane))))
      (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN bits.toNat)) := by
  rw [lanes_map_words]
  intro lane member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
  have inputWf : wf_fN (lsize (lanetype_Fnn ty))
      (Option.get! (proj_lane__1 (laneOfBits (lanetype_Fnn ty) (laneWord (lanetype_Fnn ty) bits j).toNat))) := by
    cases ty <;> exact floatOfBits_wf _ (by decide) _
  intro value allowed
  have wf := float_unary_choices_wf (lsize (lanetype_Fnn ty)) (by cases ty <;> decide) op _ inputWf value allowed
  cases ty <;> exact .lane__case_1 _ _ _ wf rfl

theorem float_unary_relation (ty : Fnn) (op : vunop_Fnn_N) (bits : BitVec 128) :
    fun_vunop_ (shapeOf (lanetype_Fnn ty)) (floatUnarySource ty op)
      (.mk_uN bits.toNat) (some (floatUnaryResults ty op bits)) := by
  have shapeWf := shapeOf_wf (lanetype_Fnn ty)
  have lanesWf := float_unary_lanes_wf ty op bits
  cases ty <;> cases op
  · apply fun_vunop_.fun_vunop__case_12
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_14
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_16
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_18
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_20
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_22
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_24
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_13
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_15
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_17
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_19
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_21
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_23
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_25
    all_goals first | rfl | exact shapeWf | exact lanesWf

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Float Unary Choices -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem lanes_roundtrip (ty : lanetype) (bits : BitVec 128) :
    inv_lanes_ (shapeOf ty) (lanes_ (shapeOf ty) (.mk_uN bits.toNat)) = .mk_uN bits.toNat := by
  change uN.mk_uN (packLanes ty (unpackLanes ty (128/lsize ty) bits.toNat)) = _
  rw [pack_unpackLanes,shapeOf_covers,Nat.mod_eq_of_lt bits.isLt]

theorem float_unary_result_member (ty : Fnn) (op : vunop_Fnn_N) (x result : BitVec 128)
    (allowed : ∀ j, j < 128/lsize (lanetype_Fnn ty) →
      floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) result j).toNat ∈
        floatUnaryChoices (lsize (lanetype_Fnn ty)) op
          (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) x j).toNat)) :
    uN.mk_uN result.toNat ∈ floatUnaryResults ty op x := by
  apply List.mem_map.mpr
  refine ⟨lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN result.toNat),?_,lanes_roundtrip _ result⟩
  rw [lanes_map_words,lanes_map_words]
  change List.map _ _ ∈ setproduct_ _ (List.map _ (List.map _ _))
  rw [List.map_map]
  apply mem_setproduct_map
  intro j member
  have chosen := allowed j (List.mem_range.mp member)
  cases ty <;> exact List.mem_map.mpr ⟨_,chosen,rfl⟩

theorem float_unary_step (ty : Fnn) (op : vunop_Fnn_N) (x result : BitVec 128)
    (allowed : ∀ j, j < 128/lsize (lanetype_Fnn ty) →
      floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) result j).toNat ∈
        floatUnaryChoices (lsize (lanetype_Fnn ty)) op
          (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) x j).toNat)) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),
      .VUNOP (shapeOf (lanetype_Fnn ty)) (floatUnarySource ty op)] [.VCONST .V128 (.mk_uN result.toNat)] := by
  have chosen := float_unary_result_member ty op x result allowed
  apply Step_pure.vunop _ _ _ _ (some (floatUnaryResults ty op x)) (float_unary_relation ty op x)
  · exact List.length_pos_of_mem chosen
  · simp
  · simpa only [Option.get!_some,List.contains_iff_mem] using chosen
  · exact const_wf x
  · exact .admininstr_case_25 _ _ (shapeOf_wf _) (float_unary_source_wf ty op)
  · exact const_wf result

end Itasca.Runtime.Spec.Simd

end
