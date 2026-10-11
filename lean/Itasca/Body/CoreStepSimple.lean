import Itasca.Body.CoreInvariant
import Itasca.Body.CoreSimple
import Itasca.Visitor.CoreVisitor
import Itasca.Body.SignedConst

open Aeneas Aeneas.Std

namespace Itasca.Core

/-- Lift a context-independent operand effect through the open frame zipper. -/
private theorem Pending.append_simple {data tokens ctx bt st token}
    (p : Pending data tokens ctx bt st token) (st' : code.OpIterState)
    (op : instr) (poly : Bool) (vals : List code.StackType) (hop : Simple token op)
    (htyped : ∀ C, wf_context C →
      Sequence.TypedPrefix C p.current.ops p.current.ctrl.polymorphic_base p.current.vals →
      Sequence.TypedPrefix C (p.current.ops ++ [op]) poly vals)
    (hctrls : st'.ctrls.val = p.parents.map Frames.Saved.ctrl ++
      [{ p.current.ctrl with polymorphic_base := poly }])
    (hvals : st'.vals.val = st.vals.val.take p.current.ctrl.value_stack_base.val ++ vals)
    (hpos : st'.pos = p.next) (hlen : vals.length ≤ p.current.vals.length + 1) :
    State data tokens ctx bt st' := by
  obtain ⟨hopen, htrace⟩ := p.opened.append (functionContext_wf ctx) token op poly vals hop htyped
    (by simpa [Frames.Saved.advance] using hctrls) hvals
  apply p.running_after st' p.parents (p.current.advance token op poly vals) hopen
    (by simpa [Frames.bodyType_advance] using p.bodyType) htrace hpos
  · obtain ⟨C, outer, _, _, hbase, _, _, hv⟩ := p.opened
    simp only [hv, hbase, List.take_left] at hvals
    simp only [hvals, hv, List.length_append]
    omega
  · obtain ⟨_, _, _, _, _, _, hc, _⟩ := p.opened
    simp [hctrls, hc]

/-- NOP consumes its opcode and preserves the open frame's represented operands. -/
theorem Pending.step_nop {data tokens ctx bt st}
    (p : Pending data tokens ctx bt st .nop) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : CoreVisitor.Total visitor) (env : module.Env) (v : V) :
    code.step visitor st data env ctx code.OP_NOP v ⦃ r => r.1 = .Ok () →
      State data tokens ctx bt r.2.1 ∧ r.2.1.pos = p.next ⦄ := by
  apply WP.spec_mono (code.step_nop.total visitor st data env ctx v hvisitor)
  intro r hr _
  rw [hr]
  have hpos : st.pos = p.next := (p.encoded.no_immediate st.pos p.pos rfl).symm
  obtain ⟨_, outer, _, _, hbase, _, hc, hv⟩ := p.opened
  refine ⟨p.append_simple st .NOP p.current.ctrl.polymorphic_base p.current.vals .nop
    (fun C hC h => h.nop hC) ?_ ?_ hpos (by omega), hpos⟩
  · simpa using hc
  · simp [hv, hbase]

/-- UNREACHABLE trims only the current segment and records the generated instruction. -/
theorem Pending.step_unreachable {data tokens ctx bt st}
    (p : Pending data tokens ctx bt st .unreachable) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : CoreVisitor.Total visitor) (env : module.Env) (v : V) :
    code.step visitor st data env ctx code.OP_UNREACHABLE v ⦃ r => r.1 = .Ok () →
      State data tokens ctx bt r.2.1 ∧ r.2.1.pos = p.next ⦄ := by
  refine WP.spec_mono (code.step_unreachable.of_read visitor st data env ctx v
    (fun _ => True) (fun _ s => State data tokens ctx bt s ∧ s.pos = p.next) ?_ hvisitor) ?_
  · obtain ⟨_, outer, _, _, hbase, _, hc, hv⟩ := p.opened
    obtain ⟨s, hr, hsvals, _, hsctrls, hspos⟩ := WP.spec_imp_exists
      (code.mark_unreachable.spec st (p.parents.map Frames.Saved.ctrl) p.current.ctrl hc
        (by simp [hbase, hv]))
    have hpos : s.pos = p.next := hspos.trans (p.encoded.no_immediate st.pos p.pos rfl).symm
    have hstate := p.append_simple s .UNREACHABLE true [] .unreachable
      (fun C hC h => h.unreachable hC) hsctrls (by simpa using hsvals) hpos (by simp)
    simp only [code.read_unreachable, hr, bind_ok, WP.spec_ok]
    exact ⟨trivial, fun _ _ => ⟨hstate, hpos⟩⟩
  · intro r hr hok
    exact (hr.2 hok).choose_spec

end Itasca.Core

namespace Itasca.Core

/-- DROP is total even at a polymorphic base and preserves the complete frame invariant on success. -/
theorem Pending.step_drop {data tokens ctx bt st}
    (p : Pending data tokens ctx bt st .drop) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : CoreVisitor.Total visitor) (env : module.Env) (v : V) :
    code.step visitor st data env ctx code.OP_DROP v ⦃ r => r.1 = .Ok () →
      State data tokens ctx bt r.2.1 ∧ r.2.1.pos = p.next ⦄ := by
  refine WP.spec_mono (code.step_drop.of_read visitor st data env ctx v
    (fun _ => True) (fun _ s => State data tokens ctx bt s ∧ s.pos = p.next) ?_ hvisitor) ?_
  · obtain ⟨_, outer, _, _, hbase, _, hctrls, hstack⟩ := p.opened
    have hb : (Control.base st).val = outer.length := by simp [Control.base, hctrls, hbase]
    have hpoly : Control.polymorphic st = p.current.ctrl.polymorphic_base := by
      simp [Control.polymorphic, hctrls]
    change code.pop_stack_type st ⦃ _ ⦄
    apply WP.spec_mono (code.pop_stack_type.segment st outer p.current.vals hstack hb)
    rintro ⟨res, s⟩ ⟨hc, hp, rest, hv, hout⟩
    dsimp only at hc hp hv hout
    refine ⟨trivial, ?_⟩
    intro t hok
    dsimp only at hok ⊢
    subst res
    change StackSemantics.Popped (Control.polymorphic st) p.current.vals t rest at hout
    rw [hpoly] at hout
    have hpos : s.pos = p.next := hp.trans (p.encoded.no_immediate st.pos p.pos rfl).symm
    refine ⟨p.append_simple s .DROP p.current.ctrl.polymorphic_base rest .drop
      (fun C hC h => hout.prefix_drop C hC p.current.ops h) ?_ ?_ hpos
      (by have := hout.length; omega), hpos⟩
    · simpa [hc] using hctrls
    · simpa [hstack, hbase] using hv
  · intro r hr hok
    exact (hr.2 hok).choose_spec

/-- I32 addition handles mixed concrete/polymorphic operands and records its exact token. -/
theorem Pending.step_i32Add {data tokens ctx bt st}
    (p : Pending data tokens ctx bt st .i32Add) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : CoreVisitor.Total visitor) (env : module.Env) (v : V) :
    code.step visitor st data env ctx code.OP_I32_ADD v ⦃ r => r.1 = .Ok () →
      State data tokens ctx bt r.2.1 ∧ r.2.1.pos = p.next ⦄ := by
  refine WP.spec_mono (code.step_i32_add.of_read visitor st data env ctx v
    (fun _ => True) (fun _ s => State data tokens ctx bt s ∧ s.pos = p.next) ?_ hvisitor) ?_
  · obtain ⟨_, outer, _, _, hbase, _, hctrls, hstack⟩ := p.opened
    have hb : (Control.base st).val = outer.length := by simp [Control.base, hctrls, hbase]
    have hpoly : Control.polymorphic st = p.current.ctrl.polymorphic_base := by
      simp [Control.polymorphic, hctrls]
    apply WP.spec_mono (code.read_binary.segment st outer p.current.vals .I32 .I32 hstack hb
      (by have := p.val_capacity; omega))
    rintro ⟨res, s⟩ ⟨hc, hp, rest, hv, hlen, hout⟩
    dsimp only at hc hp hv hlen hout
    refine ⟨trivial, ?_⟩
    intro t hok
    dsimp only at hok ⊢
    subst res
    change StackSemantics.NumericEffect (Control.polymorphic st) p.current.vals [.I32, .I32] .I32 rest at hout
    rw [hpoly] at hout
    have hpos : s.pos = p.next := hp.trans (p.encoded.no_immediate st.pos p.pos rfl).symm
    refine ⟨p.append_simple s Numeric.i32Add p.current.ctrl.polymorphic_base rest .i32Add
      (fun C hC h => hout.prefix C hC p.current.ops Numeric.i32Add h Numeric.i32Add_wf
        (Numeric.i32Add_typed C hC)) ?_ ?_ hpos hlen, hpos⟩
    · simpa [hc] using hctrls
    · simpa [hstack, hbase] using hv
  · intro r hr hok
    exact (hr.2 hok).choose_spec

/-- The decoded signed value is exactly the one in the token's binary encoding. -/
theorem Pending.step_i32Const {data tokens ctx bt st value}
    (p : Pending data tokens ctx bt st (.i32Const value)) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : CoreVisitor.Total visitor) (env : module.Env) (v : V) :
    code.step visitor st data env ctx code.OP_I32_CONST v ⦃ r => r.1 = .Ok () →
      State data tokens ctx bt r.2.1 ∧ r.2.1.pos = p.next ⦄ := by
  refine WP.spec_mono (code.step_i32_const.of_read visitor st data env ctx v
    (fun _ => True) (fun _ s => State data tokens ctx bt s ∧ s.pos = p.next) ?_ hvisitor) ?_
  · have hread := p.encoded.read_i32_const st.pos p.pos
    apply WP.spec_mono (code.read_i32_const.from_read st data value p.next hread
      (by have := p.val_capacity; omega))
    rintro ⟨res, s⟩ ⟨_, hv, hc, hp⟩
    dsimp only at hv hc hp
    obtain ⟨_, outer, _, _, hbase, _, hctrls, hstack⟩ := p.opened
    refine ⟨trivial, fun _ _ => ⟨?_, hp⟩⟩
    apply p.append_simple s (i32Const value) p.current.ctrl.polymorphic_base
      (p.current.vals ++ [.Val .I32]) (.i32Const value)
      (fun C hC h => h.i32Const hC value) _ _ hp (by simp)
    · simpa [hc] using hctrls
    · simpa [hstack, hbase, List.append_assoc] using hv
  · intro r hr hok
    exact (hr.2 hok).choose_spec

end Itasca.Core
