import Itasca.Wasm2.Control.EndTotal
import Itasca.Wasm2.Invariant

open Aeneas Aeneas.Std Result

namespace Itasca.MultiValue

noncomputable local instance : DecidableEq code.LabelKind := Classical.decEq _

/-- Factorization of the shared end continuation, checked against extraction. -/
def EndAllowed (frame : code.Ctrl) (isElse : Bool) (ins outs : List types.ValueType) : Prop :=
  if isElse then frame.kind = .Then else frame.kind = .Then → ins = outs

/-- The exact successful closing effect, including the root's discarded results. -/
def EndEffect (st s : code.BodyState) (parents : List code.Ctrl)
    (blocks : List signature.BlockType) (frame : code.Ctrl) (isElse : Bool)
    (ins outs : List types.ValueType) (outer : List code.StackType) : Prop :=
  s.core.pos = st.core.pos ∧
  if isElse then
    s.core.ctrls.val = parents ++ [{ frame with kind := .Else, polymorphic_base := false }] ∧
    s.blocks = st.blocks ∧ s.core.vals.val = outer ++ ins.map code.StackType.Val
  else
    s.core.ctrls.val = parents ∧ s.blocks.val = blocks ∧
    s.core.vals.val = if blocks = [] then outer else outer ++ outs.map code.StackType.Val

theorem end_frame_eq (st : code.BodyState) (env : module.Env) (isElse : Bool)
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
    intro he; have := congrArg UScalar.val he; simp [hc, hb] at this
  simp only [hn, ↓reduceIte]
  obtain ⟨i, hi, hiv⟩ := WP.spec_imp_exists (UScalar.sub_spec (x := alloc.vec.Vec.len st.blocks) (y := 1#usize) (by simp [hc, hb]))
  rw [hi]
  simp only [bind_ok]
  have hi' : i.val = blocks.length := by simp [hc, hb, ha] at hiv; omega
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
    simp [finishFrame, signature.BlockType.params.spec, signature.BlockType.results.spec] <;> rfl

/-- Successful closing consumes precisely a realization of the complete result vector. -/
theorem finishFrame.sound (st : code.BodyState) (env : module.Env) (isElse : Bool)
    (bt : signature.BlockType) (frame : code.Ctrl) (i n : Usize)
    (parents : List code.Ctrl) (blocks : List signature.BlockType)
    (ins outs : List types.ValueType) (outer segment : List code.StackType)
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
            simp [hctrl, hsvctrl, hsc, hc, hblocks, hbval, hb, hvals, het, hsv', hnz]⟩
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

end Itasca.MultiValue

namespace Itasca

/-- Successful `else`/`end` exposes both the semantic closing check and the
exact physical frame transition. No capacity assumption is needed for soundness. -/
theorem code.end_frame.sound (st : code.BodyState) (env : module.Env) (isElse : Bool)
    (parents : List code.Ctrl) (blocks : List signature.BlockType)
    (frame : code.Ctrl) (bt : signature.BlockType)
    (ins outs : List types.ValueType) (outer segment : List code.StackType)
    (hc : st.core.ctrls.val = parents ++ [frame])
    (hb : st.blocks.val = blocks ++ [bt]) (ha : blocks.length = parents.length)
    (hv : st.core.vals.val = outer ++ segment) (hbase : frame.value_stack_base.val = outer.length)
    (hin : MultiValue.resolve env (MultiValue.inputs bt) = some ins)
    (hout : MultiValue.resolve env (MultiValue.outputs bt) = some outs)
    (hs : Control.Shape st.core) :
    code.end_frame st env isElse ⦃ r => r.1 = .Ok () →
      MultiValue.EndAllowed frame isElse ins outs ∧
      Sequence.Realizes frame.polymorphic_base segment (outs.map Translate.valueType) ∧
      MultiValue.EndEffect st r.2 parents blocks frame isElse ins outs outer ⦄ := by
  rw [MultiValue.end_frame_eq st env isElse parents blocks frame bt hc hb ha]
  step as ⟨i, hi⟩
  have hi' : i.val = parents.length := by simp [hc, hb, ha] at hi; omega
  have hsfinish (b : Bool) := MultiValue.finishFrame.sound st env b bt frame i
    (alloc.vec.Vec.len st.blocks) parents blocks ins outs outer segment hc hb ha hi'
    (by simp [hc, hb, ha]) hv hbase hin hout hs
  cases isElse
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i hk
      step with code.same_types.spec env (MultiValue.inputs bt) (MultiValue.outputs bt)
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
      exact ⟨by simp [MultiValue.EndAllowed, hk], hr hok⟩
  · simp only [↓reduceIte]
    split
    · rename_i hk
      apply WP.spec_mono (hsfinish true)
      intro r hr hok
      exact ⟨hk, hr hok⟩
    · simp

end Itasca
