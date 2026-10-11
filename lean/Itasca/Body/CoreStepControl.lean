import Itasca.Body.ControlFlow
import Itasca.Body.CoreInvariant
import Itasca.Visitor.CoreVisitor

open Aeneas Aeneas.Std

namespace Itasca.Core

/-- Dispatching end advances the typed zipper or completes the function body. -/
theorem Pending.step_end {V : Type} {data : Slice U8} {tokens : List Token}
    {ctx : code.Context} {bodyBt : code.BlockType} {st : code.OpIterState}
    (p : Pending data tokens ctx bodyBt st .end_) (visitor : code.OpVisitor V)
    (env : module.Env) (v : V) (hvisitor : CoreVisitor.Total visitor) :
    code.step visitor st data env ctx code.OP_END v ⦃ r => r.1 = .Ok () →
      State data tokens ctx bodyBt r.2.1 ∧ r.2.1.pos = p.next ⦄ := by
  refine WP.spec_mono (code.step_end.of_read visitor st data env ctx v
    (fun _ => True) (fun _ s => State data tokens ctx bodyBt s ∧ s.pos = p.next) ?_ hvisitor) ?_
  · apply WP.spec_mono (code.read_end.frames (functionContext ctx) (functionContext_wf ctx)
      st p.parents p.current bodyBt p.opened p.bodyType (Nat.le_of_lt p.val_capacity))
    rintro ⟨result, s⟩ ⟨hp, hs⟩
    dsimp only at hp hs
    refine ⟨trivial, ?_⟩
    intro a ha
    obtain ⟨hv, hc, status⟩ := hs a ha
    have hpos : s.pos = p.next := hp.trans (p.encoded.no_immediate st.pos p.pos rfl).symm
    refine ⟨?_, hpos⟩
    rcases status with ⟨parents, current, hopen, htrace, hbody⟩ | ⟨hctrls, ops, hbody, htyped⟩
    · exact p.running_after s parents current hopen hbody htrace hpos hv (by omega)
    · exact p.closed_after s ops hctrls hbody htyped hpos hv
  · rintro r ⟨_, h⟩ hok
    obtain ⟨_, hs⟩ := h hok
    exact hs

/-- The else delimiter captures the typed first arm and starts an empty second arm. -/
theorem Pending.step_else {V : Type} {data : Slice U8} {tokens : List Token}
    {ctx : code.Context} {bodyBt : code.BlockType} {st : code.OpIterState}
    (p : Pending data tokens ctx bodyBt st .else_) (visitor : code.OpVisitor V)
    (env : module.Env) (v : V) (hvisitor : CoreVisitor.Total visitor) :
    code.step visitor st data env ctx code.OP_ELSE v ⦃ r => r.1 = .Ok () →
      State data tokens ctx bodyBt r.2.1 ∧ r.2.1.pos = p.next ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := id p.opened
  refine WP.spec_mono (code.step_else.of_read visitor st data env ctx v
    (fun _ => True) (fun _ s => State data tokens ctx bodyBt s ∧ s.pos = p.next) ?_ hvisitor) ?_
  · apply WP.spec_mono (code.read_else.realizes st (p.parents.map Frames.Saved.ctrl)
      p.current.ctrl outer p.current.vals ctrls vals base)
    rintro ⟨result, s⟩ ⟨hp, hs⟩
    dsimp only [ElseResult] at hp hs
    refine ⟨trivial, ?_⟩
    intro bt hbt
    dsimp only at hbt
    subst result
    obtain ⟨hk, rfl, hc, hv, hresults⟩ := hs
    have hf : p.current.form = .then_ := by
      rw [header.kind] at hk
      cases heq : p.current.form <;> simp_all [Frames.Form.kind]
    obtain ⟨hopen, htrace⟩ := p.opened.else_ (functionContext_wf ctx) hf hresults hc
      (by simpa [vals, base] using hv)
    have hpos : s.pos = p.next := hp.trans (p.encoded.no_immediate st.pos p.pos rfl).symm
    refine ⟨p.running_after s p.parents p.current.nextElse hopen ?_ htrace hpos ?_ ?_, hpos⟩
    · simpa [Frames.bodyType_else] using p.bodyType
    · simp only [hv, vals, List.length_append]
      omega
    · simp [hc, ctrls]
  · rintro r ⟨_, h⟩ hok
    obtain ⟨_, hs⟩ := h hok
    exact hs

private theorem read_block_from_type (st : code.OpIterState) (data : Slice U8)
    (bt : code.BlockType) (next : Usize)
    (hread : code.read_block_type data st.pos = .ok (.Ok (bt, next)))
    (hsize : st.ctrls.val.length < Usize.max) :
    code.read_block st data ⦃ r => r.1 = .Ok bt ∧ r.2.pos = next ∧
      r.2.vals = st.vals ∧ r.2.ctrls.val = st.ctrls.val ++ [Control.frame st .Block bt] ⦄ := by
  rw [code.read_block, hread]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step*
  simp_all [Control.frame]

private theorem read_loop_from_type (st : code.OpIterState) (data : Slice U8)
    (bt : code.BlockType) (next : Usize)
    (hread : code.read_block_type data st.pos = .ok (.Ok (bt, next)))
    (hsize : st.ctrls.val.length < Usize.max) :
    code.read_loop st data ⦃ r => r.1 = .Ok bt ∧ r.2.pos = next ∧
      r.2.vals = st.vals ∧ r.2.ctrls.val = st.ctrls.val ++ [Control.frame st .Loop bt] ⦄ := by
  rw [code.read_loop, hread]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step*
  simp_all [Control.frame]

theorem Pending.step_block {V : Type} {data : Slice U8} {tokens : List Token}
    {ctx : code.Context} {bodyBt bt : code.BlockType} {st : code.OpIterState}
    (p : Pending data tokens ctx bodyBt st (.block bt)) (visitor : code.OpVisitor V)
    (env : module.Env) (v : V) (hvisitor : CoreVisitor.Total visitor) :
    code.step visitor st data env ctx code.OP_BLOCK v ⦃ r => r.1 = .Ok () →
      State data tokens ctx bodyBt r.2.1 ∧ r.2.1.pos = p.next ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := id p.opened
  refine WP.spec_mono (code.step_block.of_read visitor st data env ctx v
    (fun _ => True) (fun _ s => State data tokens ctx bodyBt s ∧ s.pos = p.next) ?_ hvisitor) ?_
  · apply WP.spec_mono (read_block_from_type st data bt p.next
      (p.encoded.read_block st.pos p.pos) p.ctrl_capacity)
    rintro ⟨result, s⟩ ⟨hok, hp, hv, hc⟩
    dsimp only at hok hp hv hc
    refine ⟨trivial, ?_⟩
    intro a ha
    obtain ⟨hopen, htrace⟩ := p.opened.enter_child (st' := s) (functionContext_wf ctx) .block bt
      (.inl rfl) p.current.vals (by intro ts ht; simpa [Frames.Form.inputs] using ht)
      (by simpa [Frames.Saved.fresh, Frames.Form.kind, Control.frame, hv] using hc)
      (by simpa [vals, base] using congrArg alloc.vec.Vec.val hv)
    refine ⟨p.running_after s _ _ hopen ?_ ?_ hp ?_ ?_, hp⟩
    · simpa [Frames.bodyType_enter] using p.bodyType
    · simpa [Frames.Form.opening] using htrace
    · simp [hv]
    · simp [hc]
  · rintro r ⟨_, h⟩ hok
    obtain ⟨_, hs⟩ := h hok
    exact hs

theorem Pending.step_loop {V : Type} {data : Slice U8} {tokens : List Token}
    {ctx : code.Context} {bodyBt bt : code.BlockType} {st : code.OpIterState}
    (p : Pending data tokens ctx bodyBt st (.loop bt)) (visitor : code.OpVisitor V)
    (env : module.Env) (v : V) (hvisitor : CoreVisitor.Total visitor) :
    code.step visitor st data env ctx code.OP_LOOP v ⦃ r => r.1 = .Ok () →
      State data tokens ctx bodyBt r.2.1 ∧ r.2.1.pos = p.next ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := id p.opened
  refine WP.spec_mono (code.step_loop.of_read visitor st data env ctx v
    (fun _ => True) (fun _ s => State data tokens ctx bodyBt s ∧ s.pos = p.next) ?_ hvisitor) ?_
  · apply WP.spec_mono (read_loop_from_type st data bt p.next
      (p.encoded.read_loop st.pos p.pos) p.ctrl_capacity)
    rintro ⟨result, s⟩ ⟨hok, hp, hv, hc⟩
    dsimp only at hok hp hv hc
    refine ⟨trivial, ?_⟩
    intro a ha
    obtain ⟨hopen, htrace⟩ := p.opened.enter_child (st' := s) (functionContext_wf ctx) .loop bt
      (.inr (.inl rfl)) p.current.vals (by intro ts ht; simpa [Frames.Form.inputs] using ht)
      (by simpa [Frames.Saved.fresh, Frames.Form.kind, Control.frame, hv] using hc)
      (by simpa [vals, base] using congrArg alloc.vec.Vec.val hv)
    refine ⟨p.running_after s _ _ hopen ?_ ?_ hp ?_ ?_, hp⟩
    · simpa [Frames.bodyType_enter] using p.bodyType
    · simpa [Frames.Form.opening] using htrace
    · simp [hv]
    · simp [hc]
  · rintro r ⟨_, h⟩ hok
    obtain ⟨_, hs⟩ := h hok
    exact hs

/-- If entry suspends its parent with the consumed i32 condition in the typing derivation. -/
theorem Pending.step_if {V : Type} {data : Slice U8} {tokens : List Token}
    {ctx : code.Context} {bodyBt bt : code.BlockType} {st : code.OpIterState}
    (p : Pending data tokens ctx bodyBt st (.if_ bt)) (visitor : code.OpVisitor V)
    (env : module.Env) (v : V) (hvisitor : CoreVisitor.Total visitor) :
    code.step visitor st data env ctx code.OP_IF v ⦃ r => r.1 = .Ok () →
      State data tokens ctx bodyBt r.2.1 ∧ r.2.1.pos = p.next ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := id p.opened
  refine WP.spec_mono (code.step_if.of_read visitor st data env ctx v
    (fun _ => True) (fun _ s => State data tokens ctx bodyBt s ∧ s.pos = p.next) ?_ hvisitor) ?_
  · apply WP.spec_mono (code.read_if.from_block_type st data bt p.next outer p.current.vals
      (p.encoded.read_if st.pos p.pos) vals (by simp [Control.base, ctrls, base]) p.ctrl_capacity)
    rintro ⟨result, s⟩ ⟨hp, hs⟩
    dsimp only at hp hs
    refine ⟨trivial, ?_⟩
    intro result' heq
    dsimp only at heq
    subst result
    obtain ⟨hbt, remaining, hv, hlen, hc, hback⟩ := hs
    obtain ⟨hopen, htrace⟩ := p.opened.enter_child (st' := s) (functionContext_wf ctx) .then_ bt
      (.inr (.inr rfl)) remaining
      (by simpa [Frames.Form.inputs, Control.polymorphic, ctrls] using hback)
      (by simpa [Frames.Saved.fresh, Frames.Form.kind] using hc)
      (by simpa [vals, base] using hv)
    refine ⟨p.running_after s _ _ hopen ?_ ?_ hp ?_ ?_, hp⟩
    · simpa [Frames.bodyType_enter] using p.bodyType
    · simpa [Frames.Form.opening] using htrace
    · simp only [hv, vals, List.length_append]
      omega
    · simp [hc]
  · rintro r ⟨_, h⟩ hok
    obtain ⟨_, hs⟩ := h hok
    exact hs

end Itasca.Core
