import Itasca.Handler.ControlFlow
import Itasca.Wasm1.Frames
import Itasca.Wasm1.Invariant
import Itasca.Handler.RawControl
import Itasca.Visitor.Total

open Aeneas Aeneas.Std

namespace Itasca

/-- The extracted end handler either rejects or advances the complete typed syntax zipper. -/
@[step]
theorem code.read_end.wasm1_frames (root : context) (hroot : wf_context root)
    (st : code.OpIterState) (parents : List Wasm1.Frames.Saved) (current : Wasm1.Frames.Saved)
    (bodyBt : code.BlockType) (hopen : Wasm1.Frames.Open root st parents current)
    (hbody : Wasm1.Frames.bodyType parents current = some bodyBt)
    (hsize : st.vals.val.length + 1 ≤ Usize.max) :
    code.read_end st ⦃ r => r.2.pos = st.pos ∧
      ∀ result, r.1 = .Ok result →
        r.2.vals.val.length ≤ st.vals.val.length + 1 ∧
        r.2.ctrls.val.length ≤ st.ctrls.val.length ∧
        Wasm1.Frames.Status root bodyBt r.2 (Wasm1.Frames.trace parents current ++ [.end_]) ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := id hopen
  obtain ⟨⟨result, st'⟩, hr, hp, hsem⟩ := WP.spec_imp_exists
    (code.read_end.realizes st (parents.map Wasm1.Frames.Saved.ctrl) current.ctrl outer current.vals
      ctrls vals base hsize)
  dsimp only [EndResult] at hp hsem
  rw [hr, WP.spec_ok]
  refine ⟨hp, ?_⟩
  intro result' heq
  dsimp only at heq
  subst result
  obtain ⟨kind, bt⟩ := result'
  obtain ⟨rfl, rfl, hc, hv, hresults, hthen⟩ := hsem
  have hrslen : (Control.results current.ctrl.block_type).length ≤ 1 := by
    cases current.ctrl.block_type <;> simp [Control.results]
  refine ⟨?_, ?_, ?_⟩
  · simp only [hv, vals, List.length_append, List.length_map]
    omega
  · simp [hc, ctrls]
  · by_cases hform : current.form = .body
    · obtain ⟨hparents, htokens, htyped, hprofile⟩ := hopen.finish_body hform hresults
      have hbt : current.ctrl.block_type = bodyBt := by simpa [hparents] using hbody
      right
      refine ⟨by simpa [hparents] using hc, current.ops, htokens, ?_, ?_⟩
      simpa [hbt] using htyped
      simpa [hbt] using hprofile
    · have hex : ∃ op, Wasm1.Frames.Closed current.form current.ctrl.block_type current.ops op := by
        cases hf : current.form with
        | body => exact False.elim (hform hf)
        | block => exact ⟨_, .block _ _⟩
        | loop => exact ⟨_, .loop _ _⟩
        | then_ =>
          have hbt := hthen (by rw [header.kind, hf]; rfl)
          rw [hbt]
          exact ⟨_, .then_ _⟩
        | else_ tokens ops => exact ⟨_, .else_ _ _ _ _⟩
      obtain ⟨op, closed⟩ := hex
      obtain ⟨gps, parent, hparents, hnext, htrace⟩ := hopen.close hroot op closed hresults hc
        (by simpa [vals, base] using hv)
      left
      refine ⟨gps, _, hnext, htrace, ?_⟩
      rw [Wasm1.Frames.bodyType_close, ← hparents]
      exact hbody


end Itasca

open Aeneas Aeneas.Std

namespace Itasca.Wasm1


theorem Pending.step_end {V : Type} {data env ctx bodyBt st}
    (p : Pending data env ctx bodyBt st) (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_END) :
    code.step visitor st data env ctx code.OP_END v ⦃ r => r.1 = .Ok () → p.After r.2.1 ⦄ := by
  simp only [code.OP_END] at hbyte
  refine WP.spec_mono (code.step_end.of_read visitor st data env ctx v
    (fun _ => True) (fun _ s => p.After s) ?_ hvisitor.toCore) ?_
  · apply WP.spec_mono (code.read_end.wasm1_frames (EnvTranslation.context env ctx)
      (EnvTranslation.context_wf env ctx) st p.parents p.current bodyBt p.opened p.bodyType
      (Nat.le_of_lt p.val_capacity))
    rintro ⟨result, s⟩ ⟨hp, hs⟩
    dsimp only at hp hs
    refine ⟨trivial, ?_⟩
    intro a ha
    obtain ⟨hv, hc, status⟩ := hs a ha
    have encoded : At data p.start .end_ s.pos :=
      .no_immediate p.inbounds hbyte (by simpa [hp] using p.pos) .end_
    rcases status with ⟨parents, current, hopen, htrace, hbody⟩ | ⟨hctrls, ops, hbody, htyped, hprofile⟩
    · exact p.running_after s parents current .end_ encoded hopen hbody htrace hv (by omega)
    · exact p.closed_after s ops encoded hctrls hbody htyped hprofile hv
  · intro r hr hok
    exact (hr.2 hok).choose_spec

theorem Pending.step_else {V : Type} {data env ctx bodyBt st}
    (p : Pending data env ctx bodyBt st) (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_ELSE) :
    code.step visitor st data env ctx code.OP_ELSE v ⦃ r => r.1 = .Ok () → p.After r.2.1 ⦄ := by
  simp only [code.OP_ELSE] at hbyte
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := id p.opened
  refine WP.spec_mono (code.step_else.of_read visitor st data env ctx v
    (fun _ => True) (fun _ s => p.After s) ?_ hvisitor.toCore) ?_
  · apply WP.spec_mono (code.read_else.realizes st (p.parents.map Wasm1.Frames.Saved.ctrl)
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
      cases heq : p.current.form <;> simp_all [Wasm1.Frames.Form.kind]
    obtain ⟨hopen, htrace⟩ := p.opened.else_ (EnvTranslation.context_wf env ctx) hf hresults hc
      (by simpa [vals, base] using hv)
    have encoded : At data p.start .else_ s.pos :=
      .no_immediate p.inbounds hbyte (by simpa [hp] using p.pos) .else_
    refine p.running_after s p.parents p.current.nextElse .else_ encoded hopen ?_ htrace ?_ ?_
    · simpa [Wasm1.Frames.bodyType_else] using p.bodyType
    · simp only [hv, vals, List.length_append]
      omega
    · simp [hc, ctrls]
  · intro r hr hok
    exact (hr.2 hok).choose_spec

theorem Pending.step_block {V : Type} {data env ctx bodyBt st}
    (p : Pending data env ctx bodyBt st) (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_BLOCK) :
    code.step visitor st data env ctx code.OP_BLOCK v ⦃ r => r.1 = .Ok () → p.After r.2.1 ⦄ := by
  simp only [code.OP_BLOCK] at hbyte
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := id p.opened
  refine WP.spec_mono (code.step_block.of_read visitor st data env ctx v
    (fun _ => True) (fun _ s => p.After s) ?_ hvisitor.toCore) ?_
  · apply WP.spec_mono (code.read_block.raw_spec st data p.ctrl_capacity)
    rintro ⟨result, s⟩ hs
    dsimp only at hs
    refine ⟨trivial, ?_⟩
    intro bt hok
    obtain ⟨hd, hv, hc⟩ := hs bt hok
    obtain ⟨hopen, htrace⟩ := p.opened.enter_child (st' := s)
      (EnvTranslation.context_wf env ctx) .block bt (.inl rfl) p.current.vals
      (by intro ts ht; simpa [Wasm1.Frames.Form.inputs] using ht)
      (by simpa [Wasm1.Frames.Saved.fresh, Wasm1.Frames.Form.kind, Control.frame, hv] using hc)
      (by simpa [vals, base] using congrArg alloc.vec.Vec.val hv)
    apply p.running_after s _ _ (.block bt) (.of_block_type bt p.inbounds hbyte p.pos (.block bt) hd) hopen
    · simpa [Wasm1.Frames.bodyType_enter] using p.bodyType
    · simpa [Wasm1.Frames.Form.opening] using htrace
    · simp [hv]
    · simp [hc]
  · intro r hr hok
    exact (hr.2 hok).choose_spec

theorem Pending.step_loop {V : Type} {data env ctx bodyBt st}
    (p : Pending data env ctx bodyBt st) (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_LOOP) :
    code.step visitor st data env ctx code.OP_LOOP v ⦃ r => r.1 = .Ok () → p.After r.2.1 ⦄ := by
  simp only [code.OP_LOOP] at hbyte
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := id p.opened
  refine WP.spec_mono (code.step_loop.of_read visitor st data env ctx v
    (fun _ => True) (fun _ s => p.After s) ?_ hvisitor.toCore) ?_
  · apply WP.spec_mono (code.read_loop.raw_spec st data p.ctrl_capacity)
    rintro ⟨result, s⟩ hs
    dsimp only at hs
    refine ⟨trivial, ?_⟩
    intro bt hok
    obtain ⟨hd, hv, hc⟩ := hs bt hok
    obtain ⟨hopen, htrace⟩ := p.opened.enter_child (st' := s)
      (EnvTranslation.context_wf env ctx) .loop bt (.inr (.inl rfl)) p.current.vals
      (by intro ts ht; simpa [Wasm1.Frames.Form.inputs] using ht)
      (by simpa [Wasm1.Frames.Saved.fresh, Wasm1.Frames.Form.kind, Control.frame, hv] using hc)
      (by simpa [vals, base] using congrArg alloc.vec.Vec.val hv)
    apply p.running_after s _ _ (.loop bt) (.of_block_type bt p.inbounds hbyte p.pos (.loop bt) hd) hopen
    · simpa [Wasm1.Frames.bodyType_enter] using p.bodyType
    · simpa [Wasm1.Frames.Form.opening] using htrace
    · simp [hv]
    · simp [hc]
  · intro r hr hok
    exact (hr.2 hok).choose_spec

theorem Pending.step_if {V : Type} {data env ctx bodyBt st}
    (p : Pending data env ctx bodyBt st) (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_IF) :
    code.step visitor st data env ctx code.OP_IF v ⦃ r => r.1 = .Ok () → p.After r.2.1 ⦄ := by
  simp only [code.OP_IF] at hbyte
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := id p.opened
  refine WP.spec_mono (code.step_if.of_read visitor st data env ctx v
    (fun _ => True) (fun _ s => p.After s) ?_ hvisitor.toCore) ?_
  · apply WP.spec_mono (code.read_if.raw_spec st data outer p.current.vals vals
      (by simp [Control.base, ctrls, base]) p.ctrl_capacity)
    rintro ⟨result, s⟩ hs
    dsimp only at hs
    refine ⟨trivial, ?_⟩
    intro bt hok
    obtain ⟨hd, remaining, hv, hlen, hc, hback⟩ := hs bt hok
    obtain ⟨hopen, htrace⟩ := p.opened.enter_child (st' := s)
      (EnvTranslation.context_wf env ctx) .then_ bt (.inr (.inr rfl)) remaining
      (by simpa [Wasm1.Frames.Form.inputs, Control.polymorphic, ctrls] using hback)
      (by simpa [Wasm1.Frames.Saved.fresh, Wasm1.Frames.Form.kind] using hc)
      (by simpa [vals, base] using hv)
    apply p.running_after s _ _ (.if_ bt) (.of_block_type bt p.inbounds hbyte p.pos (.if_ bt) hd) hopen
    · simpa [Wasm1.Frames.bodyType_enter] using p.bodyType
    · simpa [Wasm1.Frames.Form.opening] using htrace
    · simp only [hv, vals, List.length_append]
      omega
    · simp [hc]
  · intro r hr hok
    exact (hr.2 hok).choose_spec

end Itasca.Wasm1
