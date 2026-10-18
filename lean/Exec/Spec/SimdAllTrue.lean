import Exec.Spec.SimdShiftSource
namespace Exec.Spec.Simd
open SpecExt.Builtins

def allTrueSource (ty : Jnn) : admininstr :=
  .VTESTOP (shapeOf (lanetype_Jnn ty)) (.mk_vtestop__0 ty (128/lsize (lanetype_Jnn ty)) .ALL_TRUE)

theorem all_true_prior (ty : Jnn) (bits : BitVec 128)
    (prior : Step_pure_before_vtestop_false [.VCONST .V128 (.mk_uN bits.toNat),allTrueSource ty]) :
    Forall (fun lane => proj_uN_0 (Option.get! (proj_lane__0 lane)) ≠ 0)
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN bits.toNat)) := by
  generalize programEq : [admininstr.VCONST .V128 (.mk_uN bits.toNat),allTrueSource ty] = program at prior
  cases prior <;> simp_all [allTrueSource,shapeOf]
  rcases programEq with ⟨_,⟨_,sizeEq⟩,_,_⟩
  subst_vars
  assumption

theorem all_true_step (ty : Jnn) (bits : BitVec 128) (answer : Bool)
    (truth : answer = true ↔ ∀ j, j < 128/lsize (lanetype_Jnn ty) →
      (vectorLane (lanetype_Jnn ty) bits j).toNat ≠ 0) :
    Step_pure [.VCONST .V128 (.mk_uN bits.toNat),allTrueSource ty]
      [.CONST .I32 (.mk_num__0 .I32 (.mk_uN (if answer then 1 else 0)))] := by
  let inputs := (List.range (128/lsize (lanetype_Jnn ty))).map
    (fun j => lane_.mk_lane__0 ty (.mk_uN (vectorLane (lanetype_Jnn ty) bits j).toNat))
  have inputEq : inputs = lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN bits.toNat) := by
    rw [vector_lanes]
    cases ty <;> rfl
  have projected : Forall (fun lane => proj_lane__0 lane ≠ none) inputs := by
    intro lane member
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
    simp [proj_lane__0]
  have inputWf : Forall (fun lane => wf_lane_ (lanetype_Jnn ty) lane) inputs := by
    intro lane member
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
    have wf := laneOfBits_wf (lanetype_Jnn ty) (vectorLane (lanetype_Jnn ty) bits j).toNat
      (BitVec.toNat_lt_twoPow_of_le (by rfl))
    cases ty <;> exact wf
  have sourceWf : wf_admininstr (allTrueSource ty) :=
    .admininstr_case_27 _ _ (shapeOf_wf _) (.vtestop__case_0 _ _ _ _ rfl)
  cases answer with
  | true =>
    apply Step_pure.vtestop_true _ _ _ inputs inputEq projected _ inputWf
      (const_wf bits) sourceWf (.admininstr_case_13 _ _ (unsigned_num_wf .I32 1 (by decide))) (shapeOf_wf _)
    intro lane member
    obtain ⟨j,valid,rfl⟩ := List.mem_map.mp member
    exact truth.mp rfl j (List.mem_range.mp valid)
  | false =>
    apply Step_pure.vtestop_false _ _ _ _ (const_wf bits) sourceWf
      (.admininstr_case_13 _ _ (unsigned_num_wf .I32 0 (by decide)))
    intro prior
    have nonzero := all_true_prior ty bits prior
    have yes : ∀ j, j < 128/lsize (lanetype_Jnn ty) →
        (vectorLane (lanetype_Jnn ty) bits j).toNat ≠ 0 := by
      intro j valid
      have member : lane_.mk_lane__0 ty (.mk_uN (vectorLane (lanetype_Jnn ty) bits j).toNat) ∈ inputs :=
        List.mem_map.mpr ⟨j,List.mem_range.mpr valid,rfl⟩
      rw [inputEq] at member
      exact nonzero _ member
    have impossible := truth.mpr yes
    cases impossible
end Exec.Spec.Simd
