import Itasca.Wasm2.Control.Total

open Aeneas Aeneas.Std Result

namespace Itasca.Control

theorem Shape.change_metadata {st s : code.OpIterState} (hs : Shape st)
    (hv : s.vals = st.vals)
    (hc : s.ctrls.val.map (fun c => c.value_stack_base.val) =
      st.ctrls.val.map (fun c => c.value_stack_base.val)) : Shape s := by
  constructor
  · have h : (st.ctrls.val.map (fun c => c.value_stack_base.val)).Pairwise (· ≤ ·) :=
      List.pairwise_map.mpr hs.ordered
    exact List.pairwise_map.mp (hc ▸ h)
  · intro c hm
    have hm' : c.value_stack_base.val ∈ st.ctrls.val.map (fun c => c.value_stack_base.val) := by
      rw [← hc]
      exact List.mem_map_of_mem hm
    obtain ⟨d, hd, he⟩ := List.mem_map.mp hm'
    simpa [hv, ← he] using hs.bounded d hd

theorem Shape.pop_ctrl {st s : code.OpIterState} (hs : Shape st)
    (hv : s.vals = st.vals) (hc : s.ctrls.val = st.ctrls.val.dropLast) : Shape s := by
  constructor
  · rw [hc]
    exact hs.ordered.sublist (List.dropLast_sublist _)
  · intro c hm
    rw [hc] at hm
    simpa [hv] using hs.bounded c (List.mem_of_mem_dropLast hm)

end Itasca.Control

namespace Itasca.Wasm2

/-- The common continuation of the extracted `end_frame` branches. The
handler proof below checks this factorization against the extracted code. -/
def finishFrame (st : code.BodyState) (env : module.Env) (isElse : Bool)
    (bt : signature.BlockType) (frame : code.Ctrl) (i n : Usize) :
    Result (core.result.Result Unit error.OpError × code.BodyState) := do
  let rt ← signature.BlockType.results bt
  let (r, ois) ← code.pop_results st.core env rt
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | .Continue _ =>
    if alloc.vec.Vec.len ois.vals != frame.value_stack_base then
      .ok (.Err .StackMismatch, { st with core := ois })
    else if isElse then
      let (c, back) ← alloc.vec.Vec.index_mut
        (core.slice.index.SliceIndexUsizeSlice code.Ctrl) ois.ctrls i
      let v := back { c with kind := .Else }
      let (c1, back1) ← alloc.vec.Vec.index_mut
        (core.slice.index.SliceIndexUsizeSlice code.Ctrl) v i
      let v1 := back1 { c1 with polymorphic_base := false }
      let rt1 ← signature.BlockType.params bt
      let (r1, ois1) ← code.push_results { ois with ctrls := v1 } env rt1
      .ok (r1, { st with core := ois1 })
    else
      let (_, v) ← alloc.vec.Vec.pop Global ois.ctrls
      let (_, v1) ← alloc.vec.Vec.pop Global st.blocks
      if n = 1#usize then
        .ok (.Ok (), { core := { ois with ctrls := v } })
      else
        let (r1, ois1) ← code.push_results { ois with ctrls := v } env rt
        .ok (r1, { core := ois1 })
  | .Break residual =>
    let r1 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      Unit (core.convert.FromSame error.OpError) residual
    .ok (r1, { st with core := ois })

set_option maxHeartbeats 1200000 in
/-- Metadata erasure preserves the original closing continuation exactly. -/
theorem end_frame_normalized (st : code.BodyState) (env : module.Env) (isElse : Bool) :
    code.end_frame st env isElse = (do
      let n := alloc.vec.Vec.len st.blocks
      if n = 0#usize then .ok (.Err .UnknownLabel, st) else
      let i ← n - 1#usize
      let bt ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice signature.BlockType) st.blocks i
      let frame ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice code.Ctrl) st.core.ctrls i
      if isElse then
        match frame.kind with
        | .Then => finishFrame st env true bt frame i n
        | _ => .ok (.Err .TypeMismatch, st)
      else
        match frame.kind with
        | .Then =>
          let ins ← signature.BlockType.params bt
          let outs ← signature.BlockType.results bt
          let r ← code.same_types env ins outs
          let cf ← core.result.Result.Insts.CoreOpsTry.branch r
          match cf with
          | .Continue equal =>
            if equal then finishFrame st env false bt frame i n
            else .ok (.Err .TypeMismatch, st)
          | .Break residual =>
            let r ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame error.OpError) residual
            .ok (r, st)
        | _ => finishFrame st env false bt frame i n) := by
  simp only [code.end_frame, code.end_frame_info, code.BodyState.blocks_len,
    code.BodyState.blocks_index, Std.bind_assoc, bind_ok]
  split
  · simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · simp only [Std.bind_assoc]
    congr 1
    funext i
    congr 1
    funext bt
    congr 1
    funext frame
    cases isElse <;> cases hk : frame.kind
    all_goals
      simp [finishFrame, alloc.vec.Vec.pop, signature.BlockType.params.spec, signature.BlockType.results.spec,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        Std.uncurry, Std.bind_assoc]
      repeat' first
        | contradiction
        | rfl
        | simp_all [Std.uncurry, Std.bind_assoc]
        | (congr 1; funext x)
        | split

@[step]
theorem finishFrame.total (st : code.BodyState) (env : module.Env) (isElse : Bool)
    (bt : signature.BlockType) (frame : code.Ctrl) (i n : Usize)
    (hs : Control.Shape st.core)
    (hi : i.val < st.core.ctrls.val.length) :
    finishFrame st env isElse bt frame i n ⦃ r =>
      Control.Shape r.2.core ∧ r.2.blocks.val.length = r.2.core.ctrls.val.length ∧
      r.2.blocks.val.length ≤ st.blocks.val.length ∧ r.2.core.pos = st.core.pos ⦄ := by
  unfold finishFrame
  simp only [signature.BlockType.results.spec, signature.BlockType.params.spec, bind_ok]
  step with code.pop_results.total st.core env (outputs bt) hs
    as ⟨r, s, hs', hc, hp, hv⟩
  step
  split
  · split
    · simp_all
    · cases isElse <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · step
        step
        have hsp : Control.Shape { s with ctrls := v } :=
          hs'.pop_ctrl rfl (by simp_all)
        step* by first | exact hsp | simp_all
      · step as ⟨c0, back0, hc0, hback0⟩
        step as ⟨c1, back1, hc1, hback1⟩ by simp_all [alloc.vec.Vec.set]
        have hsp : Control.Shape { s with ctrls := back1 { c1 with polymorphic_base := false } } := by
          refine hs'.change_metadata (s := { s with ctrls := back1 { c1 with polymorphic_base := false } }) rfl ?_
          simp_all [alloc.vec.Vec.set, List.map_set]
          rw [← List.getElem_map (f := fun c : code.Ctrl => c.value_stack_base.val)]
          exact List.set_getElem_self (by simpa using hi)
        step* by first | exact hsp | simp_all
  · step*
    simp_all

end Itasca.Wasm2

namespace Itasca

@[step]
theorem code.end_frame.total (st : code.BodyState) (env : module.Env)
    (isElse : Bool) (hs : Control.Shape st.core)
    (ha : st.blocks.val.length = st.core.ctrls.val.length) :
    code.end_frame st env isElse ⦃ r =>
      Control.Shape r.2.core ∧ r.2.blocks.val.length = r.2.core.ctrls.val.length ∧
      r.2.blocks.val.length ≤ st.blocks.val.length ∧ r.2.core.pos = st.core.pos ⦄ := by
  rw [Wasm2.end_frame_normalized]
  by_cases hn : alloc.vec.Vec.len st.blocks = 0#usize
  ·
    simp only [hn, ↓reduceIte]
    simp [hs]
  · simp only [hn, ↓reduceIte]
    step as ⟨i, hi⟩
    step as ⟨bt, hbt⟩
    step as ⟨frame, hf⟩
    have hindex : i.val < st.core.ctrls.val.length := by scalar_tac
    have finish := Wasm2.finishFrame.total st env isElse bt frame i
      (alloc.vec.Vec.len st.blocks) hs hindex
    cases isElse <;> cases hk : frame.kind <;>
      simp only [Bool.false_eq_true, ↓reduceIte]
    case false.Then =>
      simp only [signature.BlockType.params.spec, signature.BlockType.results.spec, bind_ok]
      step with code.same_types.spec env (Wasm2.inputs bt) (Wasm2.outputs bt)
      step
      split
      · split
        · exact finish
        · simp_all
      · step*
    all_goals first
      | exact finish
      | solve | simp_all

end Itasca
