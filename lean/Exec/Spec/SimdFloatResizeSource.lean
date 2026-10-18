import Exec.Spec.SimdFloatResize
namespace Exec.Spec.Simd
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
    · exact .lane__case_1 _ _ _ (Exec.Spec.float_demote_wf 64 32 (by decide) value result member) rfl
    · exact .lane__case_1 _ _ _ (Exec.Spec.float_demote_wf 32 64 (by decide) value result member) rfl
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

end Exec.Spec.Simd
