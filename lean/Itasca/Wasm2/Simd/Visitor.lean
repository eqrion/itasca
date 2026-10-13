import Itasca.Wasm2.Simd.DispatchTotal
import Itasca.Visitor.StepLift

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Simd

private theorem sub_transfer {V W : Type} (visitor : code.OpVisitor V)
    (replacement : code.OpVisitor W) (ha : FullVisitor.Accepts replacement)
    (st final : code.OpIterState) (data : Slice U8) (env : module.Env)
    (subopcode : U32) (v v' : V) (w : W)
    (h : subStep visitor st data env subopcode v = .ok (.Ok (), final, v')) :
    ∃ w', subStep replacement st data env subopcode w = .ok (.Ok (), final, w') := by
  unfold subStep at h ⊢
  rw [pure_table] at h ⊢
  cases hm : pureMeaning subopcode.val with
  | some op =>
    simp only [hm, Option.map_some, bind_ok] at h ⊢
    exact CoreVisitor.run.accepted_lift _ _ _ v w final v' h (fun _ => ha.on_simd w final subopcode)
  | none =>
    simp only [hm, Option.map_none, bind_ok] at h ⊢
    rw [lane_table] at h ⊢
    cases hl : laneMeaning subopcode.val with
    | some lane =>
      simp only [hl, Option.map_some, bind_ok] at h ⊢
      rcases he : lane.runtime with ⟨ty, count, replace⟩
      simp only [he] at h ⊢
      exact CoreVisitor.run.accepted_lift _ _ _ v w final v' h
        (fun a => ha.on_simd_lane w final subopcode a)
    | none =>
      simp only [hl, Option.map_none, bind_ok] at h ⊢
      rw [memory_table] at h ⊢
      cases hm : memoryMeaning subopcode.val with
      | some mem =>
        simp only [hm, Option.map_some, bind_ok] at h ⊢
        rcases he : mem.runtime with ⟨align, store, count⟩
        simp only [he] at h ⊢
        split at h
        · rename_i hc
          simp only [hc, if_true]
          exact CoreVisitor.run.accepted_lift _ _ _ v w final v' h
            (fun a => ha.on_simd_memory_lane w final subopcode a.1 a.2)
        · rename_i hc
          simp only [hc, if_false]
          cases store <;> simp only [Bool.false_eq_true, Bool.true_eq, if_true, if_false] at h ⊢
          all_goals exact CoreVisitor.run.accepted_lift _ _ _ v w final v' h (fun a => ha.on_simd_memory w final subopcode a)
      | none =>
        simp only [hm, Option.map_none, bind_ok] at h ⊢
        split at h
        · exact CoreVisitor.run.accepted_lift _ _ _ v w final v' h
            (fun a => ha.on_simd_const w final a.1 a.2)
        · exact CoreVisitor.run.accepted_lift _ _ _ v w final v' h
            (fun a => ha.on_simd_shuffle w final a.1 a.2)
        · simp at h

/-- Accepting hooks preserve every successful SIMD state and immediate. -/
theorem simd_transfer {V W : Type} (visitor : code.OpVisitor V)
    (replacement : code.OpVisitor W) (ha : FullVisitor.Accepts replacement)
    (st final : code.OpIterState) (data : Slice U8) (env : module.Env)
    (v v' : V) (w : W)
    (h : code.step_simd visitor st data env v = .ok (.Ok (), final, v')) :
    ∃ w', code.step_simd replacement st data env w = .ok (.Ok (), final, w') := by
  rw [code.step_simd.eq_runs] at h ⊢
  unfold prefixStep at h ⊢
  obtain ⟨r, hr⟩ := reader.read_u32_leb.total data st.pos
  simp only [hr, bind_ok] at h ⊢
  cases r with
  | Err e => simp at h
  | Ok pair =>
    obtain ⟨subopcode, next⟩ := pair
    exact sub_transfer visitor replacement ha _ final data env subopcode v v' w h

end Itasca.Wasm2.Simd
