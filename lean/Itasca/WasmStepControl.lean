import Itasca.WasmInvariant
import Itasca.WasmControlFlow
import Itasca.RawControl
import Itasca.FullVisitor

open Aeneas Aeneas.Std

namespace Itasca.Wasm

theorem Pending.step_end {V : Type} {data env ctx bodyBt st}
    (p : Pending data env ctx bodyBt st) (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_END) :
    code.step visitor st data env ctx code.OP_END v ⦃ r => r.1 = .Ok () → p.After r.2.1 ⦄ := by
  simp only [code.OP_END] at hbyte
  refine WP.spec_mono (code.step_end.of_read visitor st data env ctx v
    (fun _ => True) (fun _ s => p.After s) ?_ hvisitor.toCore) ?_
  · apply WP.spec_mono (code.read_end.wasm_frames (EnvTranslation.context env ctx)
      (EnvTranslation.context_wf env ctx) st p.parents p.current bodyBt p.opened p.bodyType
      (Nat.le_of_lt p.val_capacity))
    rintro ⟨result, s⟩ ⟨hp, hs⟩
    dsimp only at hp hs
    refine ⟨trivial, ?_⟩
    intro a ha
    obtain ⟨hv, hc, status⟩ := hs a ha
    have encoded : At data p.start .end_ s.pos :=
      .no_immediate p.inbounds hbyte (by simpa [hp] using p.pos) .end_
    rcases status with ⟨parents, current, hopen, htrace, hbody⟩ | ⟨hctrls, ops, hbody, htyped⟩
    · exact p.running_after s parents current .end_ encoded hopen hbody htrace hv (by omega)
    · exact p.closed_after s ops encoded hctrls hbody htyped hv
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
  · apply WP.spec_mono (code.read_else.realizes st (p.parents.map WasmFrames.Saved.ctrl)
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
      cases heq : p.current.form <;> simp_all [WasmFrames.Form.kind]
    obtain ⟨hopen, htrace⟩ := p.opened.else_ (EnvTranslation.context_wf env ctx) hf hresults hc
      (by simpa [vals, base] using hv)
    have encoded : At data p.start .else_ s.pos :=
      .no_immediate p.inbounds hbyte (by simpa [hp] using p.pos) .else_
    refine p.running_after s p.parents p.current.nextElse .else_ encoded hopen ?_ htrace ?_ ?_
    · simpa [WasmFrames.bodyType_else] using p.bodyType
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
      (by intro ts ht; simpa [WasmFrames.Form.inputs] using ht)
      (by simpa [WasmFrames.Saved.fresh, WasmFrames.Form.kind, Control.frame, hv] using hc)
      (by simpa [vals, base] using congrArg alloc.vec.Vec.val hv)
    apply p.running_after s _ _ (.block bt) (.of_block_type bt p.inbounds hbyte p.pos (.block bt) hd) hopen
    · simpa [WasmFrames.bodyType_enter] using p.bodyType
    · simpa [WasmFrames.Form.opening] using htrace
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
      (by intro ts ht; simpa [WasmFrames.Form.inputs] using ht)
      (by simpa [WasmFrames.Saved.fresh, WasmFrames.Form.kind, Control.frame, hv] using hc)
      (by simpa [vals, base] using congrArg alloc.vec.Vec.val hv)
    apply p.running_after s _ _ (.loop bt) (.of_block_type bt p.inbounds hbyte p.pos (.loop bt) hd) hopen
    · simpa [WasmFrames.bodyType_enter] using p.bodyType
    · simpa [WasmFrames.Form.opening] using htrace
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
      (by simpa [WasmFrames.Form.inputs, Control.polymorphic, ctrls] using hback)
      (by simpa [WasmFrames.Saved.fresh, WasmFrames.Form.kind] using hc)
      (by simpa [vals, base] using hv)
    apply p.running_after s _ _ (.if_ bt) (.of_block_type bt p.inbounds hbyte p.pos (.if_ bt) hd) hopen
    · simpa [WasmFrames.bodyType_enter] using p.bodyType
    · simpa [WasmFrames.Form.opening] using htrace
    · simp only [hv, vals, List.length_append]
      omega
    · simp [hc]
  · intro r hr hok
    exact (hr.2 hok).choose_spec

end Itasca.Wasm
