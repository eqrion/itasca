import Itasca.Wasm2.Simd.Dispatch
import Itasca.Wasm2.Simd.Tables

/-!
# Totality of the SIMD dispatcher

`simd_total` shows that the extracted `code.step_simd` never panics under a total visitor, keeps
the control stack and moves the cursor forward, for every subopcode and immediate.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Simd

private theorem run_total {A V : Type}
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (hook : V → code.OpIterState → A → Result (core.result.Result Unit error.VisitError × V))
    (v : V) (st : code.OpIterState)
    (hr : read ⦃ r => ReaderPost st r.2 ⦄)
    (hh : ∀ s a, ∃ res v', hook v s a = .ok (res, v')) :
    CoreVisitor.run read hook v ⦃ r => ReaderPost st r.2.1 ⦄ := by
  apply WP.spec_mono (CoreVisitor.run.spec read hook v (ReaderPost st) (fun _ _ => True) ?_ hh)
  · exact fun _ h => h.1
  · exact WP.spec_mono hr (fun _ h => ⟨h, by simp⟩)

theorem sub_total {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (subopcode : U32) (v : V)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max)
    (hv : FullVisitor.Total visitor) :
    subStep visitor st data env subopcode v ⦃ r => ReaderPost st r.2.1 ⦄ := by
  unfold subStep
  rw [pure_table]
  cases hm : pureMeaning subopcode.val with
  | some op =>
    simp only [Option.map_some, bind_ok]
    exact run_total _ _ v st (signature_total _ _ hs hsize) (fun s _ => hv.on_simd v s subopcode)
  | none =>
    simp only [Option.map_none, bind_ok]
    rw [lane_table]
    cases hl : laneMeaning subopcode.val with
    | some lane =>
      simp only [Option.map_some, bind_ok]
      rcases he : lane.runtime with ⟨ty, count, replace⟩
      simp only
      exact run_total _ _ v st (read_lane_total _ _ _ _ _ hs hsize)
        (fun s a => hv.on_simd_lane v s subopcode a)
    | none =>
      simp only [Option.map_none, bind_ok]
      rw [memory_table]
      cases hm : memoryMeaning subopcode.val with
      | some mem =>
        simp only [Option.map_some, bind_ok]
        rcases he : mem.runtime with ⟨align, store, count⟩
        simp only
        split
        · exact run_total _ _ v st (memory_lane_total _ _ _ _ _ _ hs hsize)
            (fun s a => hv.on_simd_memory_lane v s subopcode a.1 a.2)
        · split
          · exact run_total _ _ v st (store_total _ _ _ _ _ hs)
              (fun s a => hv.on_simd_memory v s subopcode a)
          · exact run_total _ _ v st (load_total _ _ _ _ _ hs hsize)
              (fun s a => hv.on_simd_memory v s subopcode a)
      | none =>
        simp only [Option.map_none, bind_ok]
        split
        · exact run_total _ _ v st (constant_total _ _ hs hsize)
            (fun s a => hv.on_simd_const v s a.1 a.2)
        · exact run_total _ _ v st (shuffle_total _ _ hs hsize)
            (fun s a => hv.on_simd_shuffle v s a.1 a.2)
        · simp [ReaderPost, hs]

/-- Every SIMD prefix terminates, preserves controls, and advances monotonically. -/
theorem simd_total {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (v : V)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max)
    (hv : FullVisitor.Total visitor) :
    code.step_simd visitor st data env v ⦃ r => Control.Shape r.2.1 ∧
      r.2.1.ctrls = st.ctrls ∧ st.pos.val ≤ r.2.1.pos.val ∧
      r.2.1.vals.val.length ≤ st.vals.val.length + 1 ⦄ := by
  rw [code.step_simd.eq_runs]
  unfold prefixStep
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.pos)
  rw [hr]
  simp only [bind_ok]
  cases r with
  | Err e => simp [hs]
  | Ok pair =>
    obtain ⟨subopcode, next⟩ := pair
    apply WP.spec_mono (sub_total visitor {st with pos := next} data env subopcode v
      ⟨hs.ordered, hs.bounded⟩ hsize hv)
    intro r h
    have hp := (Leb128.Decoded.span data st.pos subopcode next hd).1
    have hn : next.val ≤ r.2.1.pos.val := h.2.2.1
    exact ⟨h.1, h.2.1, by omega, h.2.2.2⟩

end Itasca.Wasm2.Simd
