import Itasca.Body.CoreInvariant
import Itasca.Body.CoreBranch
import Itasca.Visitor.CoreVisitor

open Aeneas Aeneas.Std

namespace Itasca.Core

private theorem Pending.append_result {data tokens ctx bt st token}
    (p : Pending data tokens ctx bt st token)
    (C : context) (outer : List code.StackType)
    (spine : Frames.Spine (functionContext ctx) p.parents C outer p.current.form)
    (header : Frames.Header C p.current)
    (base : p.current.ctrl.value_stack_base.val = outer.length)
    (ctrls : st.ctrls.val = p.parents.map Frames.Saved.ctrl ++ [p.current.ctrl])
    (vals : st.vals.val = outer ++ p.current.vals)
    (s : code.OpIterState) (op : instr) (poly : Bool) (newVals : List code.StackType)
    (simple : Simple token op)
    (typed : Sequence.TypedPrefix (Frames.enter C p.current.form p.current.ctrl.block_type)
      (p.current.ops ++ [op]) poly newVals)
    (hc : s.ctrls.val = p.parents.map Frames.Saved.ctrl ++
      [{ p.current.ctrl with polymorphic_base := poly }])
    (hv : s.vals.val = outer ++ newVals)
    (hp : s.pos = p.next) (hlen : newVals.length ≤ p.current.vals.length + 1) :
    State data tokens ctx bt s ∧ s.pos = p.next := by
  refine ⟨p.running_after s p.parents (p.current.advance token op poly newVals) ?_ ?_ ?_ hp ?_ ?_, hp⟩
  · exact ⟨C, outer, spine, ⟨header.kind, header.prior, .simple header.emits simple⟩,
      base, typed, hc, hv⟩
  · simpa [Frames.bodyType_advance] using p.bodyType
  · simp [Frames.trace, Frames.Saved.trace, Frames.Saved.advance, List.append_assoc]
  · simp only [hv, vals, List.length_append]
    omega
  · simp [hc, ctrls]

theorem Pending.step_br {V : Type} {data tokens ctx bt st depth}
    (p : Pending data tokens ctx bt st (.br depth))
    (visitor : code.OpVisitor V) (hvisitor : CoreVisitor.Total visitor)
    (env : module.Env) (v : V) :
    code.step visitor st data env ctx code.OP_BR v ⦃ r =>
      r.1 = .Ok () → State data tokens ctx bt r.2.1 ∧ r.2.1.pos = p.next ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals, hC, labels, returns⟩ :=
    p.opened.context (functionContext_wf ctx)
  have hlabels : (Frames.enter C p.current.form p.current.ctrl.block_type).LABELS =
      Control.labels st.ctrls.val := by simpa [functionContext] using labels
  have hencoded := reader.read_u32_leb.sound data st.pos depth p.next
    (p.encoded.read_br st.pos p.pos)
  have hread := code.read_br.prefix st data (p.parents.map Frames.Saved.ctrl) p.current.ctrl
    outer p.current.vals ctrls vals base _ hC p.current.ops typed hlabels
  have lifted := code.step_br.of_read visitor st data env ctx v (fun _ => True)
    (fun _ s => State data tokens ctx bt s ∧ s.pos = p.next) ?_ hvisitor
  · apply WP.spec_mono lifted
    intro r ⟨_, hr⟩ hok
    obtain ⟨_, hs⟩ := hr hok
    exact hs
  · apply WP.spec_mono hread
    intro r hr
    refine ⟨trivial, ?_⟩
    rintro ⟨d, resultBt⟩ hok
    obtain ⟨hdecoded, hv, hc, ht⟩ := hr d resultBt hok
    obtain ⟨hd, hpos⟩ := Leb128.Decoded.deterministic data st.pos d depth r.2.pos p.next hdecoded hencoded
    exact p.append_result C outer spine header base ctrls vals r.2 (.BR (.mk_uN depth.val)) true []
      (.br depth) (by simpa [hd] using ht) hc (by simpa using hv) hpos (by simp)

theorem Pending.step_brIf {V : Type} {data tokens ctx bt st depth}
    (p : Pending data tokens ctx bt st (.brIf depth))
    (visitor : code.OpVisitor V) (hvisitor : CoreVisitor.Total visitor)
    (env : module.Env) (v : V) :
    code.step visitor st data env ctx code.OP_BR_IF v ⦃ r =>
      r.1 = .Ok () → State data tokens ctx bt r.2.1 ∧ r.2.1.pos = p.next ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals, hC, labels, returns⟩ :=
    p.opened.context (functionContext_wf ctx)
  have hlabels : (Frames.enter C p.current.form p.current.ctrl.block_type).LABELS =
      Control.labels st.ctrls.val := by simpa [functionContext] using labels
  have hbase : (Control.base st).val = outer.length := by simp [Control.base, ctrls, base]
  have hpoly : Control.polymorphic st = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hencoded := reader.read_u32_leb.sound data st.pos depth p.next
    (p.encoded.read_brIf st.pos p.pos)
  have hread := code.read_br_if.prefix st data outer p.current.vals vals hbase
    (by have := p.val_capacity; omega) _ hC p.current.ops (by simpa [hpoly] using typed) hlabels
  have lifted := code.step_br_if.of_read visitor st data env ctx v (fun _ => True)
    (fun _ s => State data tokens ctx bt s ∧ s.pos = p.next) ?_ hvisitor
  · apply WP.spec_mono lifted
    intro r ⟨_, hr⟩ hok
    obtain ⟨_, hs⟩ := hr hok
    exact hs
  · apply WP.spec_mono hread
    intro r hr
    refine ⟨trivial, ?_⟩
    rintro ⟨d, resultBt⟩ hok
    obtain ⟨hdecoded, hc, rest, hv, hlen, ht⟩ := hr d resultBt hok
    obtain ⟨hd, hpos⟩ := Leb128.Decoded.deterministic data st.pos d depth r.2.pos p.next hdecoded hencoded
    apply p.append_result C outer spine header base ctrls vals r.2 (.BR_IF (.mk_uN depth.val))
      p.current.ctrl.polymorphic_base rest (.brIf depth)
      (by simpa [hd, hpoly] using ht) ?_ hv hpos hlen
    simpa [hc] using ctrls

theorem Pending.step_return {V : Type} {data tokens ctx bt st}
    (p : Pending data tokens ctx bt st .return_)
    (visitor : code.OpVisitor V) (hvisitor : CoreVisitor.Total visitor)
    (env : module.Env) (v : V) :
    code.step visitor st data env ctx code.OP_RETURN v ⦃ r =>
      r.1 = .Ok () → State data tokens ctx bt r.2.1 ∧ r.2.1.pos = p.next ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals, hC, labels, returns⟩ :=
    p.opened.context (functionContext_wf ctx)
  have hreturn : (Frames.enter C p.current.form p.current.ctrl.block_type).RETURN =
      some (.mk_list (ctx.results.val.map Translate.valueType)) := by
    simpa [functionContext] using returns
  have hnext : p.next = st.pos := p.encoded.no_immediate st.pos p.pos rfl
  have hread := code.read_return.prefix st ctx (p.parents.map Frames.Saved.ctrl) p.current.ctrl
    outer p.current.vals ctrls vals base _ hC p.current.ops typed hreturn
  have lifted := code.step_return.of_read visitor st data env ctx v (fun _ => True)
    (fun _ s => State data tokens ctx bt s ∧ s.pos = p.next) ?_ hvisitor
  · apply WP.spec_mono lifted
    intro r ⟨_, hr⟩ hok
    obtain ⟨_, hs⟩ := hr hok
    exact hs
  · apply WP.spec_mono hread
    intro r hr
    refine ⟨trivial, ?_⟩
    intro u hok
    cases u
    obtain ⟨hv, hc, hp, ht⟩ := hr hok
    exact p.append_result C outer spine header base ctrls vals r.2 .RETURN true []
      .return_ ht hc (by simpa using hv) (hp.trans hnext.symm) (by simp)

end Itasca.Core
