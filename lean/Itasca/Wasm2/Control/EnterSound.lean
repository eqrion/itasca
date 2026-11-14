import Itasca.Wasm2.Control.Total
import Itasca.Wasm2.LoopDispatch

/-!
Sections, each formerly its own module: EndTotal, EndSound, EndComplete, EndStep, EnterSound.
-/

/-! ## EndTotal -/

section

/-!
# Totality of frame closing

Totality of the extracted `code.end_frame`, which handles `end` and `else`. `Wasm2.finishFrame`
is the continuation shared by its branches, `Wasm2.end_frame_normalized` shows that the
extracted handler equals it, and `code.end_frame.total` shows that closing preserves
`Control.Shape` and alignment on arbitrary stacks and environments.
-/

open Aeneas Aeneas.Std Result

namespace Itasca.Control

/-- Changing only control metadata (not bases) preserves `Shape`. -/
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

/-- Popping the innermost control entry preserves `Shape`. -/
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

/-- The common continuation of the extracted `code.end_frame` branches. `end_frame_normalized`
checks this factorization against the extracted code. -/
def finishFrame (st : code.BodyState) (env : metadata.Env) (isElse : Bool)
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
theorem end_frame_normalized (st : code.BodyState) (env : metadata.Env) (isElse : Bool) :
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

/-- `finishFrame` is total and preserves frame alignment and bounds. -/
@[step]
theorem finishFrame.total (st : code.BodyState) (env : metadata.Env) (isElse : Bool)
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

/-- `code.end_frame` is total and preserves frame alignment and bounds, popping at most one frame
and leaving the cursor unchanged. -/
@[step]
theorem code.end_frame.total (st : code.BodyState) (env : metadata.Env)
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

end

/-! ## EndSound -/

section

/-!
# Soundness of frame closing

Soundness of the extracted `code.end_frame`, which handles `end` and `else`. `EndAllowed` and
`EndEffect` specify which closes are permitted and the exact physical transition, and
`code.end_frame.sound` shows that a successful close satisfies both and that the operand segment
realizes the frame's result types. Completeness is in `Wasm2/Control/EndComplete`.
-/

open Aeneas Aeneas.Std Result

namespace Itasca.Wasm2

noncomputable local instance : DecidableEq code.LabelKind := Classical.decEq _

/-- Which closes are allowed: `else` only closes a `then` frame, and `end` of a `then` frame
needs equal parameters and results (the omitted-else identity). -/
def EndAllowed (frame : code.Ctrl) (isElse : Bool) (ins outs : List wasm_types.ValueType) : Prop :=
  if isElse then frame.kind = .Then else frame.kind = .Then → ins = outs

/-- The exact successful closing effect, including the root's discarded results. -/
def EndEffect (st s : code.BodyState) (parents : List code.Ctrl)
    (blocks : List signature.BlockType) (frame : code.Ctrl) (isElse : Bool)
    (ins outs : List wasm_types.ValueType) (outer : List code.StackType) : Prop :=
  s.core.pos = st.core.pos ∧
  if isElse then
    s.core.ctrls.val = parents ++ [{ frame with kind := .Else, polymorphic_base := false }] ∧
    s.blocks = st.blocks ∧ s.core.vals.val = outer ++ ins.map code.StackType.Val
  else
    s.core.ctrls.val = parents ∧ s.blocks.val = blocks ∧
    s.core.vals.val = if blocks = [] then outer else outer ++ outs.map code.StackType.Val

/-- `code.end_frame` on a state with a known innermost frame unfolds to the kind check,
`code.same_types` for an omitted else, and `finishFrame`. -/
theorem end_frame_eq (st : code.BodyState) (env : metadata.Env) (isElse : Bool)
    (parents : List code.Ctrl) (blocks : List signature.BlockType)
    (frame : code.Ctrl) (bt : signature.BlockType)
    (hc : st.core.ctrls.val = parents ++ [frame])
    (hb : st.blocks.val = blocks ++ [bt]) (ha : blocks.length = parents.length) :
    code.end_frame st env isElse = (do
      let i ← alloc.vec.Vec.len st.blocks - 1#usize
      if isElse then
        if frame.kind = .Then then finishFrame st env true bt frame i (alloc.vec.Vec.len st.blocks)
        else .ok (.Err .TypeMismatch, st)
      else if frame.kind = .Then then
        let r ← code.same_types env (inputs bt) (outputs bt)
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | .Continue equal =>
          if equal then finishFrame st env false bt frame i (alloc.vec.Vec.len st.blocks)
          else .ok (.Err .TypeMismatch, st)
        | .Break residual =>
          let r ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame error.OpError) residual
          .ok (r, st)
      else finishFrame st env false bt frame i (alloc.vec.Vec.len st.blocks)) := by
  rw [end_frame_normalized]
  have hn : alloc.vec.Vec.len st.blocks ≠ 0#usize := by
    intro he; have := congrArg UScalar.val he; simp [hb] at this
  simp only [hn, ↓reduceIte]
  obtain ⟨i, hi, hiv⟩ := WP.spec_imp_exists (UScalar.sub_spec (x := alloc.vec.Vec.len st.blocks) (y := 1#usize) (by simp [hb]))
  rw [hi]
  simp only [bind_ok]
  have hi' : i.val = blocks.length := by simp [hb, ha] at hiv; omega
  have hindex : i.val < st.blocks.val.length := by simp [hb, hi']
  have hindex' : i.val < st.core.ctrls.val.length := by simp [hc, hi', ha]
  obtain ⟨bt', hbt', hbtv⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec st.blocks i hindex)
  obtain ⟨frame', hframe', hframev⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec st.core.ctrls i hindex')
  have ebt : bt' = bt := by simpa [hb, hi'] using hbtv
  have ef : frame' = frame := by simpa [hc, hi', ha] using hframev
  simp only [alloc.vec.Vec.index_slice_index]
  rw [hbt', bind_ok, hframe']
  simp only [ebt, ef, bind_ok]
  cases isElse <;> cases hk : frame.kind <;>
    simp [finishFrame, signature.BlockType.params.spec, signature.BlockType.results.spec]
  all_goals rfl

/-- Successful closing consumes precisely a realization of the complete result vector. -/
theorem finishFrame.sound (st : code.BodyState) (env : metadata.Env) (isElse : Bool)
    (bt : signature.BlockType) (frame : code.Ctrl) (i n : Usize)
    (parents : List code.Ctrl) (blocks : List signature.BlockType)
    (ins outs : List wasm_types.ValueType) (outer segment : List code.StackType)
    (hc : st.core.ctrls.val = parents ++ [frame])
    (hb : st.blocks.val = blocks ++ [bt]) (ha : blocks.length = parents.length)
    (hi : i.val = parents.length) (hn : n.val = blocks.length + 1)
    (hv : st.core.vals.val = outer ++ segment) (hbase : frame.value_stack_base.val = outer.length)
    (hin : resolve env (inputs bt) = some ins) (hout : resolve env (outputs bt) = some outs)
    (hs : Control.Shape st.core) :
    finishFrame st env isElse bt frame i n ⦃ r => r.1 = .Ok () →
      Sequence.Realizes frame.polymorphic_base segment (outs.map Translate.valueType) ∧
      EndEffect st r.2 parents blocks frame isElse ins outs outer ⦄ := by
  have hblocks : parents.map code.Ctrl.signature = blocks := by
    apply (List.append_inj (show parents.map code.Ctrl.signature ++ [frame.signature] =
      blocks ++ [bt] from by simpa [hc] using hb) (by simp [ha])).1
  unfold finishFrame
  simp only [signature.BlockType.results.spec, bind_ok]
  step with code.pop_results.realizes st.core env (outputs bt) outs outer segment
    hout hv (by simp [Control.base, hc, hbase]) as ⟨r, s, hsc, hsp, rest, hsv, hl, ht⟩
  have hss : Control.Shape s := hs.replace_operands hsc (by simp [Control.base, hc, hbase, hsv])
  step
  split
  · rename_i x hcont
    have hr : r = .Ok () := by cases r <;> simp_all
    split
    · simp
    · rename_i hlen
      have hrest : rest = [] := by
        have hvlen : s.vals.val.length = outer.length := by scalar_tac
        have : rest.length = 0 := by rw [hsv, List.length_append] at hvlen; omega
        exact List.eq_nil_of_length_eq_zero this
      have hres : Sequence.Realizes frame.polymorphic_base segment (outs.map Translate.valueType) := by
        simpa [Control.polymorphic, hc] using ht hr [] (by
          simp [hrest, Sequence.Realizes])
      have hsv' : s.vals.val = outer := by simpa [hrest] using hsv
      cases isElse
      · simp only [Bool.false_eq_true, ↓reduceIte]
        step as ⟨v, sv, hpopped, hsvctrl⟩
        step as ⟨v1, bv, hbpop, hbval⟩
        have hnew : Control.Shape { s with ctrls := sv } := hss.pop_ctrl rfl hsvctrl
        split
        · simp_all [EndEffect]
        · step with code.push_results.total { s with ctrls := sv } env (outputs bt) hnew
          as ⟨r1, s1, hshape, hctrl, hpos, hpush⟩
          intro hok
          obtain ⟨ts, hts, hvals⟩ := hpush hok
          have het : ts = outs := by simpa [hout] using hts.symm
          have hnz : blocks ≠ [] := by intro he; subst blocks; simp_all
          exact ⟨hres, hpos.trans hsp, by
            simp [hctrl, hsvctrl, hsc, hc, hblocks, hvals, het, hsv', hnz]⟩
      · simp only [↓reduceIte]
        step as ⟨c0, back0, hc0, hback0⟩
        step as ⟨c1, back1, hc1, hback1⟩ by simp_all [alloc.vec.Vec.set]
        have hcnew : (back1 { c1 with polymorphic_base := false }).val =
            parents ++ [{ frame with kind := .Else, polymorphic_base := false }] := by
          simp_all [alloc.vec.Vec.set]
        have hnew : Control.Shape { s with ctrls := back1 { c1 with polymorphic_base := false } } := by
          apply hss.change_metadata (s := { s with ctrls := back1 { c1 with polymorphic_base := false } }) rfl
          simp [hcnew, hsc, hc]
        simp only [signature.BlockType.params.spec, bind_ok]
        step with code.push_results.total
          { s with ctrls := back1 { c1 with polymorphic_base := false } } env (inputs bt) hnew
          as ⟨r1, s1, hshape, hctrl, hpos, hpush⟩
        intro hok
        obtain ⟨ts, hts, hvals⟩ := hpush hok
        have het : ts = ins := by simpa [hin] using hts.symm
        exact ⟨hres, hpos.trans hsp, by simp [hctrl, hcnew, hc, hvals, het, hsv']⟩
  · step*

end Itasca.Wasm2

namespace Itasca

/-- Successful `else`/`end` exposes both the semantic closing check and the
exact physical frame transition. No capacity assumption is needed for soundness. -/
theorem code.end_frame.sound (st : code.BodyState) (env : metadata.Env) (isElse : Bool)
    (parents : List code.Ctrl) (blocks : List signature.BlockType)
    (frame : code.Ctrl) (bt : signature.BlockType)
    (ins outs : List wasm_types.ValueType) (outer segment : List code.StackType)
    (hc : st.core.ctrls.val = parents ++ [frame])
    (hb : st.blocks.val = blocks ++ [bt]) (ha : blocks.length = parents.length)
    (hv : st.core.vals.val = outer ++ segment) (hbase : frame.value_stack_base.val = outer.length)
    (hin : Wasm2.resolve env (Wasm2.inputs bt) = some ins)
    (hout : Wasm2.resolve env (Wasm2.outputs bt) = some outs)
    (hs : Control.Shape st.core) :
    code.end_frame st env isElse ⦃ r => r.1 = .Ok () →
      Wasm2.EndAllowed frame isElse ins outs ∧
      Sequence.Realizes frame.polymorphic_base segment (outs.map Translate.valueType) ∧
      Wasm2.EndEffect st r.2 parents blocks frame isElse ins outs outer ⦄ := by
  rw [Wasm2.end_frame_eq st env isElse parents blocks frame bt hc hb ha]
  step as ⟨i, hi⟩
  have hi' : i.val = parents.length := by simp [hb, ha] at hi; omega
  have hsfinish (b : Bool) := Wasm2.finishFrame.sound st env b bt frame i
    (alloc.vec.Vec.len st.blocks) parents blocks ins outs outer segment hc hb ha hi'
    (by simp [hb, ha]) hv hbase hin hout hs
  cases isElse
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i hk
      step with code.same_types.spec env (Wasm2.inputs bt) (Wasm2.outputs bt)
        as ⟨r, hequal⟩
      cases r with
      | Err e => simp [hin, hout] at hequal
      | Ok equal =>
        obtain ⟨ts, us, hts, hus, he⟩ := hequal
        have ht : ts = ins := by simpa [hin] using hts.symm
        have hu : us = outs := by simpa [hout] using hus.symm
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        split
        · rename_i heq
          apply WP.spec_mono (hsfinish false)
          intro r hr hok
          exact ⟨by intro _; simpa [ht, hu] using he.mp heq, hr hok⟩
        · simp
    · rename_i hk
      apply WP.spec_mono (hsfinish false)
      intro r hr hok
      exact ⟨by simp [Wasm2.EndAllowed, hk], hr hok⟩
  · simp only [↓reduceIte]
    split
    · rename_i hk
      apply WP.spec_mono (hsfinish true)
      intro r hr hok
      exact ⟨hk, hr hok⟩
    · simp

end Itasca

end

/-! ## EndComplete -/

section

/-!
# Completeness of frame closing

Completeness of the extracted `code.end_frame` for `end` and `else`. `finishFrame.complete`
accepts when the operand segment realizes the declared results, and `code.end_frame.complete`
accepts when in addition the frame kind permits the close and an omitted else is the identity.
-/

open Aeneas Aeneas.Std Result

namespace Itasca.Wasm2

/-- Realizing the declared results is sufficient to close a frame. -/
theorem finishFrame.complete (st : code.BodyState) (env : metadata.Env) (isElse : Bool)
    (bt : signature.BlockType) (frame : code.Ctrl) (i n : Usize)
    (parents : List code.Ctrl) (blocks : List signature.BlockType)
    (ins outs : List wasm_types.ValueType) (outer segment : List code.StackType)
    (hc : st.core.ctrls.val = parents ++ [frame])
    (hb : st.blocks.val = blocks ++ [bt]) (ha : blocks.length = parents.length)
    (hi : i.val = parents.length) (hn : n.val = blocks.length + 1)
    (hv : st.core.vals.val = outer ++ segment) (hbase : frame.value_stack_base.val = outer.length)
    (hin : resolve env (inputs bt) = some ins) (hout : resolve env (outputs bt) = some outs)
    (ht : Sequence.Realizes frame.polymorphic_base segment (outs.map Translate.valueType))
    (hcap : outer.length + (if isElse then ins.length else outs.length) ≤ Usize.max) :
    finishFrame st env isElse bt frame i n ⦃ r => r.1 = .Ok () ∧
      EndEffect st r.2 parents blocks frame isElse ins outs outer ⦄ := by
  have hblocks : parents.map code.Ctrl.signature = blocks := by
    apply (List.append_inj (show parents.map code.Ctrl.signature ++ [frame.signature] =
      blocks ++ [bt] from by simpa [hc] using hb) (by simp [ha])).1
  unfold finishFrame
  simp only [signature.BlockType.results.spec, bind_ok]
  step with code.pop_results.complete st.core env (outputs bt) outs outer segment []
    hout hv (by simp [Control.base, hc, hbase]) (by simpa [Control.polymorphic, hc] using ht)
    as ⟨r, s, hok, hsc, hsp, rest, hsv, hl, hrest⟩
  have hempty : rest = [] := by
    obtain ⟨pre, suffix, hp, hs, he⟩ := hrest
    have hl := hs.length_eq
    have he := List.append_eq_nil_iff.mp he.symm
    have : rest.length = 0 := by simpa [he.2] using hl
    exact List.eq_nil_of_length_eq_zero this
  have hsv' : s.vals.val = outer := by simpa [hempty] using hsv
  have hvbase : alloc.vec.Vec.len s.vals = frame.value_stack_base := by scalar_tac
  simp only [hok, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, hvbase, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte]
  cases isElse
  · simp only [Bool.false_eq_true, ↓reduceIte]
    step as ⟨v, sv, hpopped, hsvctrl⟩
    step as ⟨v1, bv, hbpop, hbval⟩
    split
    · simp_all [EndEffect]
    · step with code.push_results.spec { s with ctrls := sv } env (outputs bt) outs
        hout (by simpa [hsv'] using hcap) as ⟨r1, s1, hr1, hv1, hc1, hp1⟩
      have hnz : blocks ≠ [] := by intro he; subst blocks; simp_all
      exact ⟨hr1, hp1.trans hsp, by simp [hc1, hsvctrl, hsc, hc, hblocks, hv1, hsv', hnz]⟩
  · simp only [↓reduceIte]
    step as ⟨c0, back0, hc0, hback0⟩
    step as ⟨c1, back1, hc1, hback1⟩ by simp_all [alloc.vec.Vec.set]
    have hcnew : (back1 { c1 with polymorphic_base := false }).val =
        parents ++ [{ frame with kind := .Else, polymorphic_base := false }] := by
      simp_all [alloc.vec.Vec.set]
    simp only [signature.BlockType.params.spec, bind_ok]
    step with code.push_results.spec
      { s with ctrls := back1 { c1 with polymorphic_base := false } } env (inputs bt) ins
      hin (by simpa [hsv'] using hcap) as ⟨r1, s1, hr1, hv1, hc1, hp1⟩
    exact ⟨hr1, hp1.trans hsp, by simp [hc1, hcnew, hc, hv1, hsv']⟩

end Itasca.Wasm2

namespace Itasca

/-- Independent frame results and the omitted-else identity force actual acceptance. -/
theorem code.end_frame.complete (st : code.BodyState) (env : metadata.Env) (isElse : Bool)
    (parents : List code.Ctrl) (blocks : List signature.BlockType)
    (frame : code.Ctrl) (bt : signature.BlockType)
    (ins outs : List wasm_types.ValueType) (outer segment : List code.StackType)
    (hc : st.core.ctrls.val = parents ++ [frame])
    (hb : st.blocks.val = blocks ++ [bt]) (ha : blocks.length = parents.length)
    (hv : st.core.vals.val = outer ++ segment) (hbase : frame.value_stack_base.val = outer.length)
    (hin : Wasm2.resolve env (Wasm2.inputs bt) = some ins)
    (hout : Wasm2.resolve env (Wasm2.outputs bt) = some outs)
    (ht : Sequence.Realizes frame.polymorphic_base segment (outs.map Translate.valueType))
    (hallowed : Wasm2.EndAllowed frame isElse ins outs)
    (hcap : outer.length + (if isElse then ins.length else outs.length) ≤ Usize.max) :
    code.end_frame st env isElse ⦃ r => r.1 = .Ok () ∧
      Wasm2.EndEffect st r.2 parents blocks frame isElse ins outs outer ⦄ := by
  rw [Wasm2.end_frame_eq st env isElse parents blocks frame bt hc hb ha]
  step as ⟨i, hi⟩
  have hi' : i.val = parents.length := by simp [hb, ha] at hi; omega
  have hsfinish := Wasm2.finishFrame.complete st env isElse bt frame i
    (alloc.vec.Vec.len st.blocks) parents blocks ins outs outer segment hc hb ha hi'
    (by simp [hb, ha]) hv hbase hin hout ht hcap
  cases isElse
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i hk
      have heq := hallowed hk
      rw [code.same_types.complete env (Wasm2.inputs bt) (Wasm2.outputs bt)
        ins hin (by simpa [heq] using hout)]
      simpa [core.result.Result.Insts.CoreOpsTry.branch] using hsfinish
    · exact hsfinish
  · have hk : frame.kind = .Then := hallowed
    simpa only [Bool.true_eq, ↓reduceIte, hk] using hsfinish

end Itasca

end

/-! ## EndStep -/

section

/-!
# `end` and `else` step

`Pending.end_after` shows that `code.end_frame` for `else` (`0x05`) and `end` (`0x0b`) preserves
`Pending`, by closing the child frame into its suspended parent or, for the body frame, finishing
the function.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

private theorem empty_spine_form {env root parents C outer form ins}
    (h : Frames.Spine env root parents C outer form ins) (he : parents = []) : form = .body := by
  cases h with
  | root => rfl
  | push => simp at he

/-- Exact child-to-parent source resumption on a non-root `end`. -/
def resumedSource (parent child : Frames.Saved) (instruction : instr) : Frames.Saved :=
  { parent with
    ops := parent.ops ++ [instruction]
    vals := parent.vals ++ child.outs.map code.StackType.Val
    tokens := parent.tokens ++ child.trace ++ [.end_] }

/-- The supplied source zipper after END, including the root completion alternative. -/
def ReaderEndZipper {data env locals index st}
    (p : Pending data env locals index st) (out : code.BodyState) : Prop :=
  (p.current.form = .body ∧ p.parents = [] ∧
    BodyTokens (Frames.trace p.parents p.current ++ [.end_]) p.current.ops ∧
    Instrs_ok (Frames.enter (bodyContext env locals p.ft) .body p.current.ins p.current.outs)
      p.current.ops (.mk_functype (.mk_list []) (.mk_list (p.current.outs.map Translate.valueType)))) ∨
  ∃ grandparents parent instruction, p.parents = grandparents ++ [parent] ∧
    Frames.Closed p.current.form p.current.bt p.current.ops instruction ∧
    Frames.Open env (bodyContext env locals p.ft) out grandparents
      (resumedSource parent p.current instruction)

/-- Exact source resumption and operand results for either closing handler. -/
def ReaderClosePost {data env locals index st}
    (p : Pending data env locals index st) (out : code.BodyState) (isElse : Bool) : Prop :=
  if isElse then
    p.current.form = .then_ ∧ At data p.start .else_ out.core.pos ∧
      Sequence.Realizes p.current.ctrl.polymorphic_base p.current.vals
        (p.current.outs.map Translate.valueType) ∧
      Frames.Open env (bodyContext env locals p.ft) out p.parents p.current.nextElse ∧ p.After out
  else
    At data p.start .end_ out.core.pos ∧
      Sequence.Realizes p.current.ctrl.polymorphic_base p.current.vals
        (p.current.outs.map Translate.valueType) ∧ ReaderEndZipper p out ∧ p.After out

/-- The actual closing handlers preserve the independent typed zipper. -/
theorem Pending.end_reader {data env locals index st} (p : Pending data env locals index st)
    (isElse : Bool) (opcode : U8) (hop : opcode = if isElse then 0x05#u8 else 0x0B#u8)
    (hbyte : data.val[p.start.val]'p.inbounds = opcode) :
    code.end_frame st env isElse ⦃ r => r.1 = .Ok () → ReaderClosePost p r.2 isElse ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
  apply WP.spec_mono (code.end_frame.sound st env isElse
    (p.parents.map Frames.Saved.ctrl) (p.parents.map Frames.Saved.bt)
    p.current.ctrl p.current.bt p.current.ins p.current.outs outer p.current.vals
    ctrls blocks (by simp) vals base header.inputs header.outputs p.opened.shape.core)
  intro r hr hok
  obtain ⟨allowed, hres, hpos, effect⟩ := hr hok
  have hroot := EnvTranslation.context_wf env ⟨locals, p.ft.results⟩
  have htypes : (bodyContext env locals p.ft).TYPES = env.types.val.map EnvTranslation.funcType := rfl
  have htake : st.core.vals.val.take p.current.ctrl.value_stack_base.val = outer := by
    rw [vals, base, List.take_left]
  cases isElse
  · have encoded : At data p.start .end_ r.2.core.pos := by
      apply At.of_immediate p.inbounds (by simpa [hop] using hbyte) p.pos Immediate.end_
      exact ⟨by simp [hpos], by simp [hpos], by have hp := p.pos; have hi := p.inbounds; rw [hpos]; omega⟩
    obtain ⟨hc, hb, hv⟩ := effect
    have hthen : p.current.form = .then_ → p.current.ins = p.current.outs := by
      intro hf
      exact allowed (by simpa [hf, Frames.Form.kind] using header.kind)
    cases hf : p.current.form with
    | body =>
      have hp : p.parents = [] := (p.opened.finish_body hf hres).1
      refine ⟨encoded, hres, .inl ⟨hf, hp, (p.opened.finish_body hf hres).2⟩, ?_⟩
      exact p.finish_body r.2 encoded (by simpa [hop] using hbyte) hf hres (by simpa [hp] using hc) (by simpa [hp] using hb)
    | block | loop | then_ | else_ thenTokens thenOps =>
      all_goals
        have closed : ∃ op, Frames.Closed p.current.form p.current.bt p.current.ops op := by
          rw [hf]; first | exact ⟨_, .block _ _⟩ | exact ⟨_, .loop _ _⟩ |
            exact ⟨_, .then_ _ _⟩ | exact ⟨_, .else_ _ _ _ _⟩
        obtain ⟨op, closed⟩ := closed
        have hn : p.parents ≠ [] := by
          intro he
          have hf' := empty_spine_form spine he
          simp_all
        obtain ⟨gps, parent, he, ho, htrace⟩ := p.opened.close hroot htypes op closed hres hthen hc hb
          (by simpa [htake, List.map_eq_nil_iff, hn] using hv)
        refine ⟨encoded, hres, .inr ⟨gps, parent, op, he, closed, ho⟩, ?_⟩
        refine p.running_after r.2 gps _ .end_ encoded ho ?_ htrace ?_
        · simpa [List.append_assoc] using (Frames.bodyType_close gps parent p.current op).trans
            (by simpa [← he] using p.bodyType)
        · simp [hb, blocks]; omega
  · have hform : p.current.form = .then_ := by
      have hk := header.kind
      have ha : p.current.ctrl.kind = .Then := allowed
      cases hf : p.current.form <;> simp_all [Frames.Form.kind]
    obtain ⟨hc, hb, hv⟩ := effect
    have encoded : At data p.start .else_ r.2.core.pos := by
      apply At.of_immediate p.inbounds (by simpa [hop] using hbyte) p.pos Immediate.else_
      exact ⟨by simp [hpos], by simp [hpos], by have hp := p.pos; have hi := p.inbounds; rw [hpos]; omega⟩
    obtain ⟨ho, ht⟩ := p.opened.else_ hroot hform hres (by simpa [Frames.Saved.nextElse] using hc)
      hb (by simpa [htake] using hv)
    refine ⟨hform, encoded, hres, ho, ?_⟩
    refine p.running_after r.2 p.parents p.current.nextElse .else_ encoded ho ?_ ht ?_
    · simpa [Frames.bodyType_else] using p.bodyType
    · simp [hb]

/-- The actual closing handlers preserve the independent typed zipper. -/
theorem Pending.end_after {data env locals index st} (p : Pending data env locals index st)
    (isElse : Bool) (opcode : U8) (hop : opcode = if isElse then 0x05#u8 else 0x0B#u8)
    (hbyte : data.val[p.start.val]'p.inbounds = opcode) :
    code.end_frame st env isElse ⦃ r => r.1 = .Ok () → p.After r.2 ⦄ := by
  apply WP.spec_mono (p.end_reader isElse opcode hop hbyte)
  intro r effect accepted
  have post := effect accepted
  cases isElse
  · exact post.2.2.2
  · exact post.2.2.2.2

end Itasca.Wasm2

end

/-! ## EnterSound -/

section

/-!
# Soundness of block entry

Soundness of the extracted `code.enter`, which opens `block`, `loop` and `if` frames.
`enterParams`, `enterArgs` and `checkBlock` factor out the pieces shared by its branches, and
`enter_eq` unfolds `code.enter` into them. `EnterEffect` is the exact semantic effect of opening a
frame, and `code.enter.sound` shows that a successful entry has that effect on a decoded block
type. Completeness is in `Wasm2/Control/EnterComplete`.
-/

open Aeneas Aeneas.Std Result

namespace Itasca.Wasm2

/-- Common parameter pop and frame setup in all extracted entry branches. -/
def enterParams (st : code.BodyState) (env : metadata.Env)
    (kind : code.LabelKind) (bt : signature.BlockType) :
    Result (core.result.Result Unit error.OpError × code.BodyState) := do
  let rt ← signature.BlockType.params bt
  let (r, s) ← code.pop_results st.core env rt
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | .Continue _ =>
    let st1 ← code.push_frame { st with core := s } kind bt
    let (r, s1) ← code.push_results st1.core env rt
    .ok (r, { st1 with core := s1 })
  | .Break residual =>
    let r ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      Unit (core.convert.FromSame error.OpError) residual
    .ok (r, { st with core := s })

/-- Entry for all forms: `if` first pops its `i32` condition, then every form runs
`enterParams`. -/
def enterArgs (st : code.BodyState) (env : metadata.Env)
    (kind : code.LabelKind) (bt : signature.BlockType) :
    Result (core.result.Result Unit error.OpError × code.BodyState) := do
  match kind with
  | .Then =>
    let (r, s) ← code.pop_with_type st.core .I32
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | .Continue _ => enterParams { st with core := s } env kind bt
    | .Break residual =>
      let r ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame error.OpError) residual
      .ok (r, { st with core := s })
  | _ => enterParams st env kind bt

/-- The validity check of an indexed block type: the index is in range and the function type is
within the limits. -/
def checkIndex (env : metadata.Env) (bt : signature.BlockType) :
    Result (core.result.Result Unit error.OpError) := do
  match bt with
  | .TypeIndex index =>
    let i ← lift (UScalar.cast .Usize index)
    if i >= alloc.vec.Vec.len env.types then .ok (.Err .UnknownType)
    else
      let ft ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice wasm_types.FuncType) env.types i
      code.check_func_type ft
  | _ => .ok (.Ok ())

/-- The block type signature checks of `code.enter`. -/
def checkBlock (env : metadata.Env) (bt : signature.BlockType) :
    Result (core.result.Result Unit error.OpError) :=
  checkIndex env bt

/-- `code.enter` unfolds to the block type read, `checkBlock` and `enterArgs`. -/
theorem enter_eq (st : code.BodyState) (data : Slice U8) (env : metadata.Env)
     (kind : code.LabelKind) :
    code.enter st data env kind = (do
      let r ← signature.read_block_type data st.core.pos
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | .Continue (bt, next) =>
        let r ← checkBlock env bt
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | .Continue _ => enterArgs { st with core := { st.core with pos := next } } env kind bt
        | .Break residual =>
          let r ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame error.OpError) residual
          .ok (r, { st with core := { st.core with pos := next } })
      | .Break residual =>
        let r ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame error.OpError) residual
        .ok (r, st)) := by
  simp only [code.enter, code.enter_info, Std.bind_assoc]
  congr 1
  funext r
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨bt, next⟩ := pair
    cases bt <;> cases kind
    all_goals
      simp only [checkBlock, checkIndex, enterArgs, enterParams,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        signature.BlockType.params, Std.uncurry, Std.bind_assoc, bind_ok]
      try dsimp only
      try simp only [Std.bind_assoc, bind_ok]
      repeat' first
        | rfl
        | simp only [Std.uncurry, Std.bind_assoc, bind_ok, core.convert.FromSame.from]
        | (congr 1; funext x; try dsimp only)
        | (split <;> try dsimp only)

    all_goals first | contradiction | simp_all [bind_ok]

@[step]
theorem checkIndex.spec (env : metadata.Env) (bt : signature.BlockType) :
    checkIndex env bt ⦃ r => r = .Ok () → ∃ ins outs,
      resolve env (inputs bt) = some ins ∧ resolve env (outputs bt) = some outs ∧
      ins.length ≤ 1000 ∧ outs.length ≤ 1000 ⦄ := by
  cases bt with
  | Empty => simp [checkIndex, resolve, inputs, outputs]
  | Value t => simp [checkIndex, resolve, inputs, outputs]
  | TypeIndex index =>
    unfold checkIndex
    step
    split
    · simp
    · step as ⟨ft, hft⟩
      step with code.check_func_type.spec ft as ⟨r, hr⟩
      have hok : r = .Ok () := by assumption
      subst r
      have hi : index.val < env.types.val.length := by scalar_tac
      exact ⟨ft.params.val, ft.results.val, by simp [resolve, inputs, hi, hft, r_post],
        by simp [resolve, outputs, hi, hft, r_post], hr⟩

@[step]
theorem checkBlock.spec (env : metadata.Env) (bt : signature.BlockType) :
    checkBlock env bt ⦃ r => r = .Ok () → ∃ ins outs, resolve env (inputs bt) = some ins ∧ resolve env (outputs bt) = some outs ∧
      ins.length ≤ 1000 ∧ outs.length ≤ 1000 ⦄ := by
  simp only [checkBlock]
  exact checkIndex.spec env bt

/-- Exact semantic effect of opening a structured frame. -/
def EnterEffect (st s : code.BodyState) (form : Frames.Form) (bt : signature.BlockType)
    (ins outs : List wasm_types.ValueType) (outer segment : List code.StackType) : Prop :=
  ∃ remaining base,
    remaining.length ≤ segment.length ∧ base.val = outer.length + remaining.length ∧
    (∀ ts, Sequence.Realizes (Control.polymorphic st.core) remaining ts →
      Sequence.Realizes (Control.polymorphic st.core) segment (ts ++ form.args ins)) ∧
    s.core.ctrls.val = st.core.ctrls.val ++ [(Frames.Saved.fresh base form bt ins outs).ctrl] ∧
    s.blocks.val = st.blocks.val ++ [bt] ∧
    s.core.vals.val = outer ++ remaining ++ ins.map code.StackType.Val

/-- Parameter popping preserves the suspended parent's input signature. -/
theorem enterParams.sound (st : code.BodyState) (env : metadata.Env)
    (form : Frames.Form) (bt : signature.BlockType) (ins outs : List wasm_types.ValueType)
    (outer segment : List code.StackType)
    (hin : resolve env (inputs bt) = some ins)
    (hv : st.core.vals.val = outer ++ segment) (hb : (Control.base st.core).val = outer.length)
    (hs : Control.Shape st.core) (hcap : st.blocks.val.length < Usize.max) :
    enterParams st env form.kind bt ⦃ r => r.1 = .Ok () →
      r.2.core.pos = st.core.pos ∧ ∃ remaining base,
      remaining.length ≤ segment.length ∧ base.val = outer.length + remaining.length ∧
      (∀ ts, Sequence.Realizes (Control.polymorphic st.core) remaining ts →
        Sequence.Realizes (Control.polymorphic st.core) segment (ts ++ ins.map Translate.valueType)) ∧
      r.2.core.ctrls.val = st.core.ctrls.val ++ [(Frames.Saved.fresh base form bt ins outs).ctrl] ∧
      r.2.blocks.val = st.blocks.val ++ [bt] ∧
      r.2.core.vals.val = outer ++ remaining ++ ins.map code.StackType.Val ⦄ := by
  unfold enterParams
  simp only [signature.BlockType.params.spec, bind_ok]
  step with code.pop_results.realizes st.core env (inputs bt) ins outer segment hin hv hb
    as ⟨r, s, hc, hp, remaining, hv', hl, ht⟩
  have hs' : Control.Shape s := hs.replace_operands hc (by simp [hb, hv'])
  step
  split
  · have hok : r = .Ok () := by cases r <;> simp_all
    step with code.push_frame.spec { st with core := s } form.kind bt (by simpa [hc] using hcap)
      as ⟨s1, hc1, hv1, hp1, hb1⟩
    have hs1 : Control.Shape s1.core := shape_push hs' form.kind bt hc1 hv1
    step with code.push_results.total s1.core env (inputs bt) hs1
      as ⟨r1, s2, hs2, hc2, hp2, hpush⟩
    intro hok1
    obtain ⟨ts, hts, hvs⟩ := hpush hok1
    have he : ts = ins := by simpa [hin] using hts.symm
    refine ⟨hp2.trans (hp1.trans hp), remaining, alloc.vec.Vec.len s.vals, hl,
      by simp [hv'], ht hok, ?_, by simpa [hc2, hc] using hb1, ?_⟩
    · simp [hc2, hc1, hc, Frames.Saved.fresh, Wasm2.frame]
    · simpa [he, hv1, hv'] using hvs
  · step*

theorem enterArgs.sound (st : code.BodyState) (env : metadata.Env)
    (form : Frames.Form) (bt : signature.BlockType) (ins outs : List wasm_types.ValueType)
    (outer segment : List code.StackType) (initial : form.Initial)
    (hin : resolve env (inputs bt) = some ins)
    (hv : st.core.vals.val = outer ++ segment) (hb : (Control.base st.core).val = outer.length)
    (hs : Control.Shape st.core) (hcap : st.blocks.val.length < Usize.max) :
    enterArgs st env form.kind bt ⦃ r => r.1 = .Ok () →
      r.2.core.pos = st.core.pos ∧ EnterEffect st r.2 form bt ins outs outer segment ⦄ := by
  rcases initial with rfl | rfl | rfl
  · simpa [enterArgs, Frames.Form.kind, EnterEffect, Frames.Form.args] using
      enterParams.sound st env .block bt ins outs outer segment hin hv hb hs hcap
  · simpa [enterArgs, Frames.Form.kind, EnterEffect, Frames.Form.args] using
      enterParams.sound st env .loop bt ins outs outer segment hin hv hb hs hcap
  · simp only [enterArgs, Frames.Form.kind]
    step with code.pop_with_type.realizes st.core outer segment .I32 hv hb
      as ⟨r, s, hc, hp, rest, hv', hl, ht⟩
    step
    split
    · have hs' : Control.Shape s := hs.replace_operands hc (by simp [hb, hv'])
      have hbs : (Control.base s).val = outer.length := by simpa [Control.base, hc] using hb
      apply WP.spec_mono (enterParams.sound { st with core := s } env .then_ bt ins outs outer rest
        hin hv' hbs hs' (by simpa [hc] using hcap))
      intro result hresult hok
      obtain ⟨hpos, remaining, base, hlen, hbase, hback, hctrl, hblocks, hvals⟩ := hresult hok
      refine ⟨hpos.trans hp, remaining, base, hlen.trans hl, hbase, ?_, ?_, by simpa [hc] using hblocks, hvals⟩
      · intro ts hts
        have hr : ∃ t, r = .Ok t := by cases r <;> simp_all
        obtain ⟨t, hr⟩ := hr
        have hremaining : Sequence.Realizes (Control.polymorphic s) remaining ts := by
          simpa [Control.polymorphic, hc] using hts
        rw [hr] at ht
        have hpop := ht.2 (ts ++ ins.map Translate.valueType) (by
          simpa [Control.polymorphic, hc] using hback ts hremaining)
        simpa [Frames.Form.args, List.append_assoc, Translate.valueType] using hpop
      · simpa [hc] using hctrl
    · step*

end Itasca.Wasm2

namespace Itasca

/-- A successful `code.enter` decodes a block type whose signature resolves within the limits and
opens the frame with effect `EnterEffect`. -/
theorem code.enter.sound (st : code.BodyState) (data : Slice U8) (env : metadata.Env)
     (form : Wasm2.Frames.Form) (initial : form.Initial)
    (outer segment : List code.StackType)
    (hv : st.core.vals.val = outer ++ segment) (hb : (Control.base st.core).val = outer.length)
    (hs : Control.Shape st.core) (hcap : st.blocks.val.length < Usize.max) :
    code.enter st data env form.kind ⦃ r => r.1 = .Ok () → ∃ bt ins outs,
      Wasm2.BlockDecoded data st.core.pos bt r.2.core.pos ∧
      Wasm2.resolve env (Wasm2.inputs bt) = some ins ∧
      Wasm2.resolve env (Wasm2.outputs bt) = some outs ∧
      ins.length ≤ 1000 ∧ outs.length ≤ 1000 ∧
      Wasm2.EnterEffect st r.2 form bt ins outs outer segment ⦄ := by
  rw [Wasm2.enter_eq]
  step with signature.read_block_type.spec data st.core.pos as ⟨r, hdecoded⟩
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨bt, next⟩ := pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with Wasm2.checkBlock.spec env bt as ⟨r, hcheck⟩
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok u =>
      obtain ⟨ins, outs, hin, hout, hip, hop⟩ := hcheck (by cases u; rfl)
      simp only [bind_ok]
      apply WP.spec_mono (Wasm2.enterArgs.sound { st with core := { st.core with pos := next } }
        env form bt ins outs outer segment initial hin hv hb ⟨hs.ordered, hs.bounded⟩ hcap)
      intro result hresult hok
      obtain ⟨hpos, heffect⟩ := hresult hok
      exact ⟨bt, ins, outs, hpos ▸ hdecoded, hin, hout, hip, hop, heffect⟩

end Itasca

end
