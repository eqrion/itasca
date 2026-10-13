import Itasca.Wasm2.Control.EndSound

open Aeneas Aeneas.Std Result

namespace Itasca.MultiValue

/-- Realizing the declared results is sufficient to close a frame. -/
theorem finishFrame.complete (st : code.BodyState) (env : module.Env) (isElse : Bool)
    (bt : signature.BlockType) (frame : code.Ctrl) (i n : Usize)
    (parents : List code.Ctrl) (blocks : List signature.BlockType)
    (ins outs : List types.ValueType) (outer segment : List code.StackType)
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
      exact ⟨hr1, hp1.trans hsp, by simp [hc1, hsvctrl, hsc, hc, hblocks, hbval, hb, hv1, hsv', hnz]⟩
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

end Itasca.MultiValue

namespace Itasca

/-- Independent frame results and the omitted-else identity force actual acceptance. -/
theorem code.end_frame.complete (st : code.BodyState) (env : module.Env) (isElse : Bool)
    (parents : List code.Ctrl) (blocks : List signature.BlockType)
    (frame : code.Ctrl) (bt : signature.BlockType)
    (ins outs : List types.ValueType) (outer segment : List code.StackType)
    (hc : st.core.ctrls.val = parents ++ [frame])
    (hb : st.blocks.val = blocks ++ [bt]) (ha : blocks.length = parents.length)
    (hv : st.core.vals.val = outer ++ segment) (hbase : frame.value_stack_base.val = outer.length)
    (hin : MultiValue.resolve env (MultiValue.inputs bt) = some ins)
    (hout : MultiValue.resolve env (MultiValue.outputs bt) = some outs)
    (ht : Sequence.Realizes frame.polymorphic_base segment (outs.map Translate.valueType))
    (hallowed : MultiValue.EndAllowed frame isElse ins outs)
    (hcap : outer.length + (if isElse then ins.length else outs.length) ≤ Usize.max) :
    code.end_frame st env isElse ⦃ r => r.1 = .Ok () ∧
      MultiValue.EndEffect st r.2 parents blocks frame isElse ins outs outer ⦄ := by
  rw [MultiValue.end_frame_eq st env isElse parents blocks frame bt hc hb ha]
  step as ⟨i, hi⟩
  have hi' : i.val = parents.length := by simp [hc, hb, ha] at hi; omega
  have hsfinish := MultiValue.finishFrame.complete st env isElse bt frame i
    (alloc.vec.Vec.len st.blocks) parents blocks ins outs outer segment hc hb ha hi'
    (by simp [hc, hb, ha]) hv hbase hin hout ht hcap
  cases isElse
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i hk
      have heq := hallowed hk
      rw [code.same_types.complete env (MultiValue.inputs bt) (MultiValue.outputs bt)
        ins hin (by simpa [heq] using hout)]
      simpa [core.result.Result.Insts.CoreOpsTry.branch] using hsfinish
    · exact hsfinish
  · have hk : frame.kind = .Then := hallowed
    simpa only [Bool.true_eq, ↓reduceIte, hk] using hsfinish

end Itasca
