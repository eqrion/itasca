import Itasca.Runtime.Spec.Simd.FloatUnary
import Itasca.Runtime.Spec.FloatPromote
import Itasca.Runtime.Spec.FloatConvert

/-!
Source-rule algebra for floating-point lane promotion and demotion. Lane/list calculations establish the generated source operation and its reduction step, consumed by source-machine and interpreter correspondence proofs.
-/

/-! ## Simd Float Resize -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

inductive FloatResize where | demote | promote

def FloatResize.input : FloatResize → Fnn | .demote => .F64 | .promote => .F32

def FloatResize.output : FloatResize → Fnn | .demote => .F32 | .promote => .F64

def floatResizeChoices : FloatResize → fN → List fN
  | .demote,a => demote__ 64 32 a
  | .promote,a => promote__ 32 64 a

def floatResizeSource (kind : FloatResize) : vcvtop__ :=
  match kind with
  | .demote => .mk_vcvtop___3 .F64 2 .F32 4 (.DEMOTE .ZERO)
  | .promote => .mk_vcvtop___3 .F32 4 .F64 2 .PROMOTELOW

theorem float_resize_source_wf (kind : FloatResize) :
    wf_vcvtop__ (shapeOf (lanetype_Fnn kind.input)) (shapeOf (lanetype_Fnn kind.output)) (floatResizeSource kind) := by
  cases kind <;> apply wf_vcvtop__.vcvtop___case_3
  · exact .vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_0 _ _ _ _ _ (by decide)
  · rfl
  · rfl
  · exact .vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_1 _ _ _ _ (by decide)
  · rfl
  · rfl

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Float Resize Source -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

def floatResizeLaneChoices (kind : FloatResize) (a : fN) : List lane_ :=
  Map (lane_.mk_lane__1 kind.output) (floatResizeChoices kind a)

def floatResizeInputs (kind : FloatResize) (x : BitVec 128) : List lane_ :=
  (List.range 2).map (fun j => laneOfBits (lanetype_Fnn kind.input) (laneWord (lanetype_Fnn kind.input) x j).toNat)

def floatResizeChoicesList (kind : FloatResize) (x : BitVec 128) : List (Option (List lane_)) :=
  (List.range 2).map (fun j => some (floatResizeLaneChoices kind
    (floatOfBits (lsize (lanetype_Fnn kind.input)) (laneWord (lanetype_Fnn kind.input) x j).toNat)))

def floatResizePadding (kind : FloatResize) : List (List lane_) :=
  match kind with
  | .demote => List.replicate 2 [.mk_lane__1 .F32 (floatOfBits 32 0)]
  | .promote => []

def floatResizeProducts (kind : FloatResize) (x : BitVec 128) : List (List lane_) :=
  setproduct_ lane_ (Map Option.get! (floatResizeChoicesList kind x) ++ floatResizePadding kind)

theorem float_resize_lane_relation (kind : FloatResize) (value : fN) :
    fun_lcvtop__ (shapeOf (lanetype_Fnn kind.input)) (shapeOf (lanetype_Fnn kind.output)) (floatResizeSource kind)
      (.mk_lane__1 kind.input value) (some (floatResizeLaneChoices kind value)) := by
  have wf : Forall (fun result => wf_lane_ (lanetype_Fnn kind.output) (.mk_lane__1 kind.output result)) (floatResizeChoices kind value) := by
    intro result member
    cases kind
    · exact .lane__case_1 _ _ _ (Itasca.Runtime.Spec.float_demote_wf 64 32 (by decide) value result member) rfl
    · exact .lane__case_1 _ _ _ (Itasca.Runtime.Spec.float_demote_wf 32 64 (by decide) value result member) rfl
  cases kind
  · exact .fun_lcvtop___case_29 _ _ _ _ _ _ rfl wf rfl rfl
  · exact .fun_lcvtop___case_34 _ _ _ _ _ _ rfl wf rfl rfl

theorem float_resize_lists_relation (kind : FloatResize) (x : BitVec 128) :
    Forall₂ (fun choices input => fun_lcvtop__ (shapeOf (lanetype_Fnn kind.input))
      (shapeOf (lanetype_Fnn kind.output)) (floatResizeSource kind) input choices)
      (floatResizeChoicesList kind x) (floatResizeInputs kind x) := by
  apply forall2_map
  intro j member
  cases kind <;> exact float_resize_lane_relation _ _

theorem float_resize_product_member (kind : FloatResize) (x result : BitVec 128)
    (allowed : ∀ j, j < 2 →
      floatOfBits (lsize (lanetype_Fnn kind.output)) (laneWord (lanetype_Fnn kind.output) result j).toNat ∈
        floatResizeChoices kind (floatOfBits (lsize (lanetype_Fnn kind.input)) (laneWord (lanetype_Fnn kind.input) x j).toNat))
    (zeroed : ∀ j, 2 ≤ j → j < 128/lsize (lanetype_Fnn kind.output) → laneWord (lanetype_Fnn kind.output) result j = 0) :
    lanes_ (shapeOf (lanetype_Fnn kind.output)) (.mk_uN result.toNat) ∈ floatResizeProducts kind x := by
  rw [lanes_map_words]
  cases kind
  · change (List.range 4).map _ ∈ setproduct_ lane_ ((List.range 4).map (fun j =>
      if j < 2 then floatResizeLaneChoices .demote (floatOfBits 64 (laneWord .F64 x j).toNat)
      else [.mk_lane__1 .F32 (floatOfBits 32 0)]))
    apply mem_setproduct_map
    intro j member
    by_cases valid : j < 2
    · rw [if_pos valid]
      exact List.mem_map.mpr ⟨_,allowed j valid,rfl⟩
    · rw [if_neg valid]
      have zero := zeroed j (by omega) (List.mem_range.mp member)
      change laneWord .F32 result j = 0 at zero
      change lane_.mk_lane__1 .F32 (floatOfBits 32 (laneWord .F32 result j).toNat) ∈ _
      rw [zero]
      exact List.mem_cons_self
  · change (List.range 2).map _ ∈ setproduct_ lane_ ((List.range 2).map (fun j =>
      floatResizeLaneChoices .promote (floatOfBits 32 (laneWord .F32 x j).toNat)))
    apply mem_setproduct_map
    intro j member
    exact List.mem_map.mpr ⟨_,allowed j (List.mem_range.mp member),rfl⟩

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Float Resize Step -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

theorem float_resize_vector_relation (kind : FloatResize) (x result : BitVec 128)
    (selected : lanes_ (shapeOf (lanetype_Fnn kind.output)) (.mk_uN result.toNat) ∈ floatResizeProducts kind x) :
    fun_vcvtop__ (shapeOf (lanetype_Fnn kind.input)) (shapeOf (lanetype_Fnn kind.output)) (floatResizeSource kind)
      (.mk_uN x.toNat) (some (.mk_uN result.toNat)) := by
  let choices := floatResizeChoicesList kind x
  let inputs := floatResizeInputs kind x
  let products := floatResizeProducts kind x
  have nonempty : Forall (fun c => c ≠ none) choices := by
    intro c member
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
    simp
  have lengths : choices.length = inputs.length := by
    simp [choices,inputs,floatResizeChoicesList,floatResizeInputs]
  have member : (.mk_uN result.toNat) ∈ Map (inv_lanes_ (shapeOf (lanetype_Fnn kind.output))) products :=
    List.mem_map.mpr ⟨_,selected,lanes_roundtrip _ result⟩
  have wf := unsigned_wf_of_lt 128 result.toNat result.isLt
  cases kind
  · apply fun_vcvtop__.fun_vcvtop___case_2 .F64 2 .F32 4 (floatResizeSource .demote)
      (.mk_uN x.toNat) (.mk_uN result.toNat) inputs products (.mk_num__1 .F32 (floatOfBits 32 0))
      (some (.mk_lane__1 .F32 (floatOfBits 32 0))) choices (some (some .ZERO))
    · apply fun_zero.fun_zero_case_2
      · decide
      · exact .fun_fzero_case_0 _ (floatOfBits_wf 32 (by decide) 0)
      · exact Itasca.Runtime.Spec.float_num_wf .F32 _ (floatOfBits_wf 32 (by decide) _)
    · constructor; exact .lane__case_1 _ _ _ (floatOfBits_wf 32 (by decide) _) rfl
    · exact lengths
    · exact float_resize_lists_relation .demote x
    · exact .fun_zeroop_case_33 _ _ _ _ _ rfl rfl
    · simp
    · rfl
    · change inputs = lanes_ (shapeOf .F64) (.mk_uN x.toNat)
      rw [lanes_map_words]; rfl
    · exact nonempty
    · simp
    · rfl
    · exact List.length_pos_of_mem member
    · simpa only [List.contains_iff_mem,FloatResize.output,lanetype_Fnn,shapeOf,lsize,size,valtype_numtype,Option.get!_some] using member
    · exact wf
    · exact shape_of_wf _
    · exact shape_of_wf _
  · apply fun_vcvtop__.fun_vcvtop___case_1 .F32 4 .F64 2 (floatResizeSource .promote)
      (.mk_uN x.toNat) (.mk_uN result.toNat) .LOW inputs products choices (some (some .LOW))
    · exact lengths
    · exact float_resize_lists_relation .promote x
    · exact .fun_halfop_case_38 _ _ _ _ rfl rfl
    · simp
    · rfl
    · change inputs = List.take 2 (List.drop (fun_half .LOW 0 2) (lanes_ (shapeOf .F32) (.mk_uN x.toNat)))
      rw [lanes_map_words]; rfl
    · exact nonempty
    · rfl
    · exact List.length_pos_of_mem member
    · simpa only [List.contains_iff_mem,FloatResize.output,lanetype_Fnn,shapeOf,lsize,size,valtype_numtype,Option.get!_some] using member
    · exact wf
    · exact shape_of_wf _
    · exact shape_of_wf _

theorem float_resize_step (kind : FloatResize) (x result : BitVec 128)
    (allowed : ∀ j, j < 2 →
      floatOfBits (lsize (lanetype_Fnn kind.output)) (laneWord (lanetype_Fnn kind.output) result j).toNat ∈
        floatResizeChoices kind (floatOfBits (lsize (lanetype_Fnn kind.input)) (laneWord (lanetype_Fnn kind.input) x j).toNat))
    (zeroed : ∀ j, 2 ≤ j → j < 128/lsize (lanetype_Fnn kind.output) → laneWord (lanetype_Fnn kind.output) result j = 0) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),
      .VCVTOP (shapeOf (lanetype_Fnn kind.output)) (shapeOf (lanetype_Fnn kind.input)) (floatResizeSource kind)]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  have selected := float_resize_product_member kind x result allowed zeroed
  apply Step_pure.vcvtop _ _ _ _ _ (some (.mk_uN result.toNat))
  · exact float_resize_vector_relation kind x result selected
  · simp
  · rfl
  · exact const_wf x
  · apply wf_admininstr.admininstr_case_39
    · exact shape_of_wf _
    · exact shape_of_wf _
    · exact float_resize_source_wf kind
  · exact const_wf result

end Itasca.Runtime.Spec.Simd

end
