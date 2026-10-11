import Itasca.MultiValue.ScalarMemory
import Itasca.MultiValue.Invariant
import Itasca.MultiValue.ScalarContext
import Itasca.Body.WasmStepEnv

open Aeneas Aeneas.Std

namespace Itasca.MultiValue

private theorem Pending.append_scalar {data env locals index st}
    (p : Pending data env locals index st)
    (C : context) (outer : List code.StackType)
    (spine : Frames.Spine env (bodyContext env locals p.ft) p.parents C outer p.current.form p.current.ins)
    (header : Frames.Header env C p.current)
    (base : p.current.ctrl.value_stack_base.val = outer.length)
    (_ctrls : st.core.ctrls.val = p.parents.map Frames.Saved.ctrl ++ [p.current.ctrl])
    (_vals : st.core.vals.val = outer ++ p.current.vals)
    (s : code.OpIterState) (op : instr) (poly : Bool) (newVals : List code.StackType)
    (hwf : wf_instr op) (encoded : Wasm.At data p.start (.plain op) s.pos)
    (typed : TypedPrefix (Frames.enter C p.current.form p.current.ins p.current.outs)
      ((p.current.form.params p.current.ins).map Translate.valueType)
      (p.current.ops ++ [op]) poly newVals)
    (hc : s.ctrls.val = p.parents.map Frames.Saved.ctrl ++
      [{ p.current.ctrl with polymorphic_base := poly }])
    (hv : s.vals.val = outer ++ newVals)
    (_hlen : newVals.length ≤ p.current.vals.length + 1) : p.After {st with core := s} := by
  have hb := p.opened
  obtain ⟨_, _, _, _, _, _, _, blocks, _⟩ := hb
  exact p.append_result C outer spine header base {st with core := s} op poly newVals hwf
    (At.plain encoded) typed hc (by simpa [hc, _ctrls] using blocks) hv

private theorem Pending.append_scalar_simple {data env locals index st}
    (p : Pending data env locals index st)
    (s : code.OpIterState) (op : instr) (poly : Bool) (vals : List code.StackType)
    (hwf : wf_instr op) (encoded : Wasm.At data p.start (.plain op) s.pos)
    (htyped : ∀ C, wf_context C →
      TypedPrefix C ((p.current.form.params p.current.ins).map Translate.valueType)
        p.current.ops p.current.ctrl.polymorphic_base p.current.vals →
      TypedPrefix C ((p.current.form.params p.current.ins).map Translate.valueType)
        (p.current.ops ++ [op]) poly vals)
    (hctrls : s.ctrls.val = p.parents.map Frames.Saved.ctrl ++
      [{ p.current.ctrl with polymorphic_base := poly }])
    (hvals : s.vals.val = st.core.vals.val.take p.current.ctrl.value_stack_base.val ++ vals)
    (hlen : vals.length ≤ p.current.vals.length + 1) : p.After {st with core := s} := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, stack⟩ := id p.opened
  apply p.append_scalar C outer spine header base ctrls stack s op poly vals hwf encoded
    (htyped _ (Frames.enter_wf _ (spine.context_wf (EnvTranslation.context_wf env ⟨locals, p.ft.results⟩)) _ _ _) typed)
    hctrls _ hlen
  simpa [stack, base] using hvals

end Itasca.MultiValue

namespace Itasca.MultiValue


/-- NOP accepts arbitrary unread suffixes and records its opcode byte. -/
theorem Pending.step_nop {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V) (hsize : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_NOP) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_NOP v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  apply WP.spec_mono (code.step_nop.total visitor st.core data env ⟨locals, p.ft.results⟩ v hvisitor.toCore)
  intro r hr _
  rw [hr]
  obtain ⟨_, outer, _, _, hbase, _, hc, _, hv⟩ := p.opened
  apply p.append_scalar_simple st.core .NOP p.current.ctrl.polymorphic_base p.current.vals .instr_case_0
    (.no_immediate p.inbounds (by simpa [global_simps] using hbyte) p.pos .nop)
    (fun C hC h => h.nop hC) _ _ (by omega)
  · simpa using hc
  · simp [hv, hbase]

/-- UNREACHABLE trims the current frame and records the exact byte. -/
theorem Pending.step_unreachable {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V) (hsize : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_UNREACHABLE) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_UNREACHABLE v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  refine WP.spec_mono (code.step_unreachable.of_read visitor st.core data env ⟨locals, p.ft.results⟩ v
    (fun _ => True) (fun _ s => p.After {st with core := s}) ?_ hvisitor.toCore) ?_
  · obtain ⟨_, outer, _, _, hbase, _, hc, _, hv⟩ := p.opened
    obtain ⟨s, hr, hsvals, _, hsctrls, hspos⟩ := WP.spec_imp_exists
      (code.mark_unreachable.spec st.core (p.parents.map Frames.Saved.ctrl) p.current.ctrl hc
        (by simp [hbase, hv]))
    have encoded : Wasm.At data p.start (.plain .UNREACHABLE) s.pos :=
      .no_immediate p.inbounds (by simpa [global_simps] using hbyte)
        (by simpa [hspos] using p.pos) .unreachable
    have hafter := p.append_scalar_simple s .UNREACHABLE true [] .instr_case_1 encoded
      (fun C hC h => h.unreachable hC) hsctrls (by simpa using hsvals) (by simp)
    simp only [code.read_unreachable, hr, bind_ok, WP.spec_ok]
    exact ⟨trivial, fun _ _ => hafter⟩
  · intro r hr hok
    exact (hr.2 hok).choose_spec

/-- DROP covers concrete and polymorphic operands, and may reject an empty stack. -/
theorem Pending.step_drop {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V) (hsize : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_DROP) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_DROP v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  refine WP.spec_mono (code.step_drop.of_read visitor st.core data env ⟨locals, p.ft.results⟩ v
    (fun _ => True) (fun _ s => p.After {st with core := s}) ?_ hvisitor.toCore) ?_
  · obtain ⟨_, outer, _, _, hbase, _, hctrls, _, hstack⟩ := p.opened
    have hb : (Control.base st.core).val = outer.length := by simp [Control.base, hctrls, hbase]
    have hpoly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
      simp [Control.polymorphic, hctrls]
    change code.pop_stack_type st.core ⦃ _ ⦄
    apply WP.spec_mono (code.pop_stack_type.segment st.core outer p.current.vals hstack hb)
    rintro ⟨res, s⟩ ⟨hc, hp, rest, hv, hout⟩
    dsimp only at hc hp hv hout
    refine ⟨trivial, ?_⟩
    intro t hok
    dsimp only at hok ⊢
    subst res
    change StackSemantics.Popped (Control.polymorphic st.core) p.current.vals t rest at hout
    rw [hpoly] at hout
    have encoded : Wasm.At data p.start (.plain .DROP) s.pos :=
      .no_immediate p.inbounds (by simpa [global_simps] using hbyte)
        (by simpa [hp] using p.pos) .drop
    apply p.append_scalar_simple s .DROP p.current.ctrl.polymorphic_base rest .instr_case_2 encoded
      (fun C hC h => hout.multi_prefix_drop C hC p.current.ops h) _ _
      (by have := hout.length; omega)
    · simpa [hc] using hctrls
    · simpa [hstack, hbase] using hv
  · intro r hr hok
    exact (hr.2 hok).choose_spec

end Itasca.MultiValue

namespace Itasca.MultiValue


/-- The i32 constant step terminates on arbitrary immediate bytes and preserves the invariant on success. -/
theorem Pending.step_i32Const {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V) (hsize : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_I32_CONST) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_I32_CONST v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  refine WP.spec_mono (code.step_i32_const.of_read visitor st.core data env ⟨locals, p.ft.results⟩ v
    (fun _ => True) (fun _ s => p.After {st with core := s}) ?_ hvisitor.toCore) ?_
  · apply WP.spec_mono (code.read_i32_const.spec st.core data hsize)
    rintro ⟨res, s⟩ ⟨hc, hout⟩
    dsimp only at hc hout
    refine ⟨trivial, ?_⟩
    intro value hok
    dsimp only at hok ⊢
    subst res
    obtain ⟨hd, hv⟩ := hout
    obtain ⟨_, outer, _, _, hbase, _, hctrls, _, hstack⟩ := p.opened
    have encoded : Wasm.At data p.start (.plain (Core.i32Const value)) s.pos :=
      .of_s32 value p.inbounds (by simpa [global_simps] using hbyte) p.pos hd
    apply p.append_scalar_simple s (Core.i32Const value) p.current.ctrl.polymorphic_base
      (p.current.vals ++ [.Val .I32]) (Core.i32Const_wf value) encoded
      (fun C hC h => h.i32Const hC value) _ _ (by simp)
    · simpa [hc] using hctrls
    · simpa [hstack, hbase, List.append_assoc] using hv
  · intro r hr hok
    exact (hr.2 hok).choose_spec

/-- The i64 constant step terminates on arbitrary immediate bytes and preserves the invariant on success. -/
theorem Pending.step_i64Const {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V) (hsize : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_I64_CONST) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_I64_CONST v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  refine WP.spec_mono (code.step_i64_const.of_read visitor st.core data env ⟨locals, p.ft.results⟩ v
    (fun _ => True) (fun _ s => p.After {st with core := s}) ?_ (hvisitor.on_i64_const v)) ?_
  · apply WP.spec_mono (code.read_i64_const.spec st.core data hsize)
    rintro ⟨res, s⟩ ⟨hc, hout⟩
    dsimp only at hc hout
    refine ⟨trivial, ?_⟩
    intro value hok
    dsimp only at hok ⊢
    subst res
    obtain ⟨hd, hv⟩ := hout
    obtain ⟨_, outer, _, _, hbase, _, hctrls, _, hstack⟩ := p.opened
    have encoded : Wasm.At data p.start (.plain (ScalarConst.i64 value)) s.pos :=
      .of_s64 value p.inbounds (by simpa [global_simps] using hbyte) p.pos hd
    apply p.append_scalar_simple s (ScalarConst.i64 value) p.current.ctrl.polymorphic_base
      (p.current.vals ++ [.Val .I64]) (ScalarConst.i64_wf value) encoded
      (fun C hC h => h.i64Const hC value) _ _ (by simp)
    · simpa [hc] using hctrls
    · simpa [hstack, hbase, List.append_assoc] using hv
  · intro r hr hok
    exact (hr.2 hok).choose_spec

/-- The f32 constant step terminates on arbitrary immediate bytes and preserves the invariant on success. -/
theorem Pending.step_f32Const {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V) (hsize : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_F32_CONST) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_F32_CONST v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  refine WP.spec_mono (code.step_f32_const.of_read visitor st.core data env ⟨locals, p.ft.results⟩ v
    (fun _ => True) (fun _ s => p.After {st with core := s}) ?_ (hvisitor.on_f32_const v)) ?_
  · apply WP.spec_mono (code.read_f32_const.spec st.core data hsize)
    rintro ⟨res, s⟩ ⟨hc, hout⟩
    dsimp only at hc hout
    refine ⟨trivial, ?_⟩
    intro value hok
    dsimp only at hok ⊢
    subst res
    obtain ⟨hd, hv⟩ := hout
    obtain ⟨_, outer, _, _, hbase, _, hctrls, _, hstack⟩ := p.opened
    have encoded : Wasm.At data p.start (.plain (ScalarConst.f32 value)) s.pos :=
      .of_f32 value p.inbounds (by simpa [global_simps] using hbyte) p.pos hd
    apply p.append_scalar_simple s (ScalarConst.f32 value) p.current.ctrl.polymorphic_base
      (p.current.vals ++ [.Val .F32]) (ScalarConst.f32_wf value) encoded
      (fun C hC h => h.f32Const hC value) _ _ (by simp)
    · simpa [hc] using hctrls
    · simpa [hstack, hbase, List.append_assoc] using hv
  · intro r hr hok
    exact (hr.2 hok).choose_spec

/-- The f64 constant step terminates on arbitrary immediate bytes and preserves the invariant on success. -/
theorem Pending.step_f64Const {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V) (hsize : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_F64_CONST) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_F64_CONST v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  refine WP.spec_mono (code.step_f64_const.of_read visitor st.core data env ⟨locals, p.ft.results⟩ v
    (fun _ => True) (fun _ s => p.After {st with core := s}) ?_ (hvisitor.on_f64_const v)) ?_
  · apply WP.spec_mono (code.read_f64_const.spec st.core data hsize)
    rintro ⟨res, s⟩ ⟨hc, hout⟩
    dsimp only at hc hout
    refine ⟨trivial, ?_⟩
    intro value hok
    dsimp only at hok ⊢
    subst res
    obtain ⟨hd, hv⟩ := hout
    obtain ⟨_, outer, _, _, hbase, _, hctrls, _, hstack⟩ := p.opened
    have encoded : Wasm.At data p.start (.plain (ScalarConst.f64 value)) s.pos :=
      .of_f64 value p.inbounds (by simpa [global_simps] using hbyte) p.pos hd
    apply p.append_scalar_simple s (ScalarConst.f64 value) p.current.ctrl.polymorphic_base
      (p.current.vals ++ [.Val .F64]) (ScalarConst.f64_wf value) encoded
      (fun C hC h => h.f64Const hC value) _ _ (by simp)
    · simpa [hc] using hctrls
    · simpa [hstack, hbase, List.append_assoc] using hv
  · intro r hr hok
    exact (hr.2 hok).choose_spec

end Itasca.MultiValue

namespace Itasca.MultiValue


/-- Every numeric opcode extends the generated typing derivation under the current frame context. -/
theorem Pending.step_numeric_mapped {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V) (hsize : st.core.vals.val.length < Usize.max) (opcode : U8) (op : Numeric.Operation)
    (hbyte : data.val[p.start.val]'p.inbounds = opcode)
    (hmap : Numeric.opcodeMeaning opcode = some op) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ opcode v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, stack⟩ := id p.opened
  have hC := Frames.enter_wf C (spine.context_wf (EnvTranslation.context_wf env ⟨locals, p.ft.results⟩))
    p.current.form p.current.ins p.current.outs
  have hbase : (Control.base st.core).val = outer.length := by simp [Control.base, ctrls, base]
  have hpoly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  apply WP.spec_mono (code.step.numeric_multi_prefix visitor st.core data env ⟨locals, p.ft.results⟩ opcode op outer
    p.current.vals v _ hC p.current.ops (by simpa [hpoly] using typed) hmap stack hbase
    hsize hvisitor)
  rintro ⟨res, s, v'⟩ ⟨hc, hp, after, hv, hlen, hout⟩ hok
  dsimp only at hc hp hv hlen hout hok ⊢
  have encoded : Wasm.At data p.start (.plain op.instruction) s.pos :=
    .no_immediate p.inbounds hbyte (by simpa [hp] using p.pos) (.numeric opcode op hmap)
  apply p.append_scalar C outer spine header base ctrls stack s op.instruction
    p.current.ctrl.polymorphic_base after op.wellFormed encoded _ _ hv hlen
  · simpa [hpoly] using hout hok
  · simpa [hc] using ctrls

/-- Unmapped high opcodes terminate with rejection; mapped scalar opcodes preserve the invariant. -/
theorem Pending.step_numeric {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V) (hsize : st.core.vals.val.length < Usize.max) (opcode : U8)
    (hbyte : data.val[p.start.val]'p.inbounds = opcode) (hlow : 0x45 ≤ opcode.val) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ opcode v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  cases hm : Numeric.opcodeMeaning opcode with
  | none =>
    rw [code.step.numeric_dispatch visitor st.core data env ⟨locals, p.ft.results⟩ opcode v hlow,
      code.step_numeric.unrecognized visitor st.core opcode v hm]
    simp
  | some op => exact p.step_numeric_mapped visitor hvisitor v hsize opcode op hbyte hm

/-- SELECT preserves its joined concrete/bottom result and exact opcode provenance. -/
theorem Pending.step_select {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V) (hsize : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_SELECT) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_SELECT v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, stack⟩ := id p.opened
  have hC := Frames.enter_wf C (spine.context_wf (EnvTranslation.context_wf env ⟨locals, p.ft.results⟩))
    p.current.form p.current.ins p.current.outs
  have hbase : (Control.base st.core).val = outer.length := by simp [Control.base, ctrls, base]
  have hpoly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  apply WP.spec_mono (code.step_select.multi_prefix visitor st.core data env ⟨locals, p.ft.results⟩ outer
    p.current.vals v _ hC p.current.ops (by simpa [hpoly] using typed) stack hbase
    hsize hvisitor)
  rintro ⟨res, s, v'⟩ ⟨hc, hp, after, hv, hlen, hout⟩ hok
  dsimp only at hc hp hv hlen hout hok ⊢
  have encoded : Wasm.At data p.start (.plain (.SELECT none)) s.pos :=
    .no_immediate p.inbounds (by simpa [global_simps] using hbyte)
      (by simpa [hp] using p.pos) .select
  apply p.append_scalar C outer spine header base ctrls stack s (.SELECT none)
    p.current.ctrl.polymorphic_base after (.instr_case_3 _) encoded _ _ hv hlen
  · simpa [hpoly] using hout hok
  · simpa [hc] using ctrls

end Itasca.MultiValue

namespace Itasca.MultiValue


private theorem run_after {A V : Type} {data env locals index st}
    (p : Pending data env locals index st)
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (hook : V → code.OpIterState → A → Result (core.result.Result Unit error.VisitError × V))
    (v : V) (hread : read ⦃ r => ∀ a, r.1 = .Ok a → p.After {st with core := r.2} ⦄)
    (hhook : ∀ s a, ∃ res v', hook v s a = .ok (res, v')) :
    CoreVisitor.run read hook v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  refine WP.spec_mono (CoreVisitor.run.spec read hook v (fun _ => True) (fun _ s => p.After {st with core := s})
    (WP.spec_mono hread (fun _ h => ⟨trivial, h⟩)) hhook) ?_
  intro r h hr
  obtain ⟨_, ha⟩ := h.2 hr
  exact ha

private theorem Pending.index_post_after {data env locals index st} (p : Pending data env locals index st)
    (C : context) (outer : List code.StackType)
    (spine : Frames.Spine env (bodyContext env locals p.ft) p.parents C outer p.current.form p.current.ins)
    (header : Frames.Header env C p.current)
    (base : p.current.ctrl.value_stack_base.val = outer.length)
    (ctrls : st.core.ctrls.val = p.parents.map Frames.Saved.ctrl ++ [p.current.ctrl])
    (vals : st.core.vals.val = outer ++ p.current.vals)
    (opcode : U8) (op : U32 → instr) (hbyte : data.val[p.start.val]'p.inbounds = opcode)
    (hwf : ∀ idx, wf_instr (op idx))
    (himm : ∀ idx bytes, Leb128.Encoding bytes idx.val → Wasm.Immediate opcode (.plain (op idx)) bytes)
    (r : core.result.Result U32 error.OpError × code.OpIterState)
    (hpost : Scalar.IndexPost ((p.current.form.params p.current.ins).map Translate.valueType) data st.core outer p.current.vals
      (Frames.enter C p.current.form p.current.ins p.current.outs) p.current.ops op r)
    (idx : U32) (hr : r.1 = .Ok idx)
    : p.After {st with core := r.2} := by
  obtain ⟨hd, hc, rest, hv, hl, ht⟩ := hpost idx hr
  have hpoly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  apply p.append_scalar C outer spine header base ctrls vals r.2 (op idx)
    p.current.ctrl.polymorphic_base rest (hwf idx) _ (by simpa [hpoly] using ht) _ hv hl
  · obtain ⟨bytes, hs, hn, hb, he⟩ := hd
    exact .of_immediate p.inbounds hbyte p.pos (himm idx bytes he) ⟨hs, hn, hb⟩
  · simp [hc, ctrls]

theorem Pending.step_local_get {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hsize : st.core.vals.val.length < Usize.max) (hvisitor : FullVisitor.Total visitor)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x20#u8) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_LOCAL_GET v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hpoly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ⟨locals, p.ft.results⟩ (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (EnvTranslation.Matches.root env ⟨locals, p.ft.results⟩)).enter _
  rw [code.step_local_get.dispatch]
  apply run_after p _ _ v _ (hvisitor.on_local_get v)
  refine WP.spec_mono (code.read_local_get.multi_prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    hsize _ hC p.current.ops (by simpa [hpoly] using typed)) ?_
  intro r hr idx hi
  exact p.index_post_after C outer spine header base ctrls vals 0x20#u8 _ hbyte
    (fun idx => .instr_case_43 _ (EnvTranslation.index_wf idx))
    (fun idx _ he => .localGet idx he) r hr idx hi

theorem Pending.step_local_set {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hsize : st.core.vals.val.length < Usize.max) (hvisitor : FullVisitor.Total visitor)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x21#u8) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_LOCAL_SET v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hpoly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ⟨locals, p.ft.results⟩ (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (EnvTranslation.Matches.root env ⟨locals, p.ft.results⟩)).enter _
  rw [code.step_local_set.dispatch]
  apply run_after p _ _ v _ (hvisitor.on_local_set v)
  refine WP.spec_mono (code.read_local_set.multi_prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    (by simpa [Control.base, ctrls] using base) _ hC p.current.ops (by simpa [hpoly] using typed)) ?_
  intro r hr idx hi
  exact p.index_post_after C outer spine header base ctrls vals 0x21#u8 _ hbyte
    (fun idx => .instr_case_44 _ (EnvTranslation.index_wf idx))
    (fun idx _ he => .localSet idx he) r hr idx hi

theorem Pending.step_local_tee {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hsize : st.core.vals.val.length < Usize.max) (hvisitor : FullVisitor.Total visitor)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x22#u8) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_LOCAL_TEE v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hpoly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ⟨locals, p.ft.results⟩ (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (EnvTranslation.Matches.root env ⟨locals, p.ft.results⟩)).enter _
  rw [code.step_local_tee.dispatch]
  apply run_after p _ _ v _ (hvisitor.on_local_tee v)
  refine WP.spec_mono (code.read_local_tee.multi_prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    (by simpa [Control.base, ctrls] using base)
    hsize _ hC p.current.ops (by simpa [hpoly] using typed)) ?_
  intro r hr idx hi
  exact p.index_post_after C outer spine header base ctrls vals 0x22#u8 _ hbyte
    (fun idx => .instr_case_45 _ (EnvTranslation.index_wf idx))
    (fun idx _ he => .localTee idx he) r hr idx hi

theorem Pending.step_global_get {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hsize : st.core.vals.val.length < Usize.max) (hvisitor : FullVisitor.Total visitor)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x23#u8) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_GLOBAL_GET v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hpoly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ⟨locals, p.ft.results⟩ (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (EnvTranslation.Matches.root env ⟨locals, p.ft.results⟩)).enter _
  rw [code.step_global_get.dispatch]
  apply run_after p _ _ v _ (hvisitor.on_global_get v)
  refine WP.spec_mono (code.read_global_get.multi_prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    hsize _ hC p.current.ops (by simpa [hpoly] using typed)) ?_
  intro r hr idx hi
  exact p.index_post_after C outer spine header base ctrls vals 0x23#u8 _ hbyte
    (fun idx => .instr_case_46 _ (EnvTranslation.index_wf idx))
    (fun idx _ he => .globalGet idx he) r hr idx hi

theorem Pending.step_global_set {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hsize : st.core.vals.val.length < Usize.max) (hvisitor : FullVisitor.Total visitor)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x24#u8) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_GLOBAL_SET v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hpoly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ⟨locals, p.ft.results⟩ (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (EnvTranslation.Matches.root env ⟨locals, p.ft.results⟩)).enter _
  rw [code.step_global_set.dispatch]
  apply run_after p _ _ v _ (hvisitor.on_global_set v)
  refine WP.spec_mono (code.read_global_set.multi_prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    (by simpa [Control.base, ctrls] using base) _ hC p.current.ops (by simpa [hpoly] using typed)) ?_
  intro r hr idx hi
  exact p.index_post_after C outer spine header base ctrls vals 0x24#u8 _ hbyte
    (fun idx => .instr_case_47 _ (EnvTranslation.index_wf idx))
    (fun idx _ he => .globalSet idx he) r hr idx hi

private theorem Pending.reserved_post_after {data env locals index st} (p : Pending data env locals index st)
    (C : context) (outer : List code.StackType)
    (spine : Frames.Spine env (bodyContext env locals p.ft) p.parents C outer p.current.form p.current.ins)
    (header : Frames.Header env C p.current)
    (base : p.current.ctrl.value_stack_base.val = outer.length)
    (ctrls : st.core.ctrls.val = p.parents.map Frames.Saved.ctrl ++ [p.current.ctrl])
    (vals : st.core.vals.val = outer ++ p.current.vals)
    (opcode : U8) (op : instr) (hbyte : data.val[p.start.val]'p.inbounds = opcode)
    (hwf : wf_instr op) (himm : Wasm.Immediate opcode (.plain op) [0#u8])
    (r : core.result.Result Unit error.OpError × code.OpIterState)
    (hpost : Scalar.ReservedPost ((p.current.form.params p.current.ins).map Translate.valueType) data st.core outer p.current.vals
      (Frames.enter C p.current.form p.current.ins p.current.outs) p.current.ops op r)
    (hr : r.1 = .Ok ())
    : p.After {st with core := r.2} := by
  obtain ⟨⟨hp, hz, hn⟩, hc, rest, hv, hl, ht⟩ := hpost hr
  have hpoly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  apply p.append_scalar C outer spine header base ctrls vals r.2 op
    p.current.ctrl.polymorphic_base rest hwf _ (by simpa [hpoly] using ht) _ hv hl
  · exact .of_immediate p.inbounds hbyte p.pos himm (.byte data st.core.pos r.2.pos 0#u8 hp hz hn)
  · simp [hc, ctrls]

theorem Pending.step_memory_size {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hsize : st.core.vals.val.length < Usize.max) (hvisitor : FullVisitor.Total visitor)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x3F#u8) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_MEMORY_SIZE v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hpoly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ⟨locals, p.ft.results⟩ (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (EnvTranslation.Matches.root env ⟨locals, p.ft.results⟩)).enter _
  rw [code.step_memory_size.dispatch]
  apply run_after p _ _ v _ (fun s _ => hvisitor.on_memory_size v s)
  refine WP.spec_mono (code.read_memory_size.multi_prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    hsize _ hC p.current.ops (by simpa [hpoly] using typed)) ?_
  intro r hr u hi
  cases u
  exact p.reserved_post_after C outer spine header base ctrls vals 0x3F#u8 _ hbyte
    .instr_case_62 .memorySize r hr hi

theorem Pending.step_memory_grow {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hsize : st.core.vals.val.length < Usize.max) (hvisitor : FullVisitor.Total visitor)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x40#u8) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_MEMORY_GROW v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hpoly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ⟨locals, p.ft.results⟩ (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (EnvTranslation.Matches.root env ⟨locals, p.ft.results⟩)).enter _
  rw [code.step_memory_grow.dispatch]
  apply run_after p _ _ v _ (fun s _ => hvisitor.on_memory_grow v s)
  refine WP.spec_mono (code.read_memory_grow.multi_prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    (by simpa [Control.base, ctrls] using base) hsize
    _ hC p.current.ops (by simpa [hpoly] using typed)) ?_
  intro r hr u hi
  cases u
  exact p.reserved_post_after C outer spine header base ctrls vals 0x40#u8 _ hbyte
    .instr_case_63 .memoryGrow r hr hi

theorem Pending.step_memory {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hsize : st.core.vals.val.length < Usize.max) (hvisitor : FullVisitor.Total visitor)
    (opcode : U8) (operation : MemoryMeaning.Operation)
    (hbyte : data.val[p.start.val]'p.inbounds = opcode)
    (hrow : MemoryMeaning.opcodeMeaning opcode = some operation) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ opcode v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hpoly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ⟨locals, p.ft.results⟩ (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (EnvTranslation.Matches.root env ⟨locals, p.ft.results⟩)).enter _
  have hb : (Control.base st.core).val = outer.length := by simpa [Control.base, ctrls] using base
  have hread : (if operation.store then code.read_store st.core data env operation.ty operation.naturalAlign
      else code.read_load st.core data env operation.ty operation.naturalAlign) ⦃
        Scalar.MemoryPost ((p.current.form.params p.current.ins).map Translate.valueType) data st.core outer p.current.vals
          (Frames.enter C p.current.form p.current.ins p.current.outs) p.current.ops operation.op ⦄ := by
    cases hs : operation.store with
    | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact code.read_load.multi_prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals hb
          hsize _ hC p.current.ops (by simpa [hpoly] using typed)
          opcode operation hrow hs
    | true =>
        simp only [↓reduceIte]
        exact code.read_store.multi_prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals hb
          _ hC p.current.ops (by simpa [hpoly] using typed) opcode operation hrow hs
  rw [code.step_memory.dispatch visitor st.core data env ⟨locals, p.ft.results⟩ v opcode operation hrow]
  apply run_after p _ _ v _ (fun s arg => hvisitor.visit_memory v s opcode arg)
  refine WP.spec_mono hread ?_
  intro r hr arg hi
  obtain ⟨⟨middle, halign, hoffset⟩, hc, rest, hv, hl, ht⟩ := hr arg hi
  have hwf : wf_instr (operation.op arg) := ht.wellFormed _ (by simp)
  apply p.append_scalar C outer spine header base ctrls vals r.2 (operation.op arg)
    p.current.ctrl.polymorphic_base rest hwf _ (by simpa [hpoly] using ht) _ hv hl
  · obtain ⟨alignment, ha, hna, hba, hea⟩ := halign
    obtain ⟨offset, ho, hno, hbo, heo⟩ := hoffset
    exact .of_immediate p.inbounds hbyte p.pos (.memory opcode operation arg hrow hea heo)
      ((show Wasm.BytesAt data st.core.pos alignment middle from ⟨ha, hna, hba⟩).append ⟨ho, hno, hbo⟩)
  · simp [hc, ctrls]

end Itasca.MultiValue
namespace Itasca.MultiValue

/-- Successful shared scalar dispatch preserves the multi-value control zipper
and appends exactly the independently decoded instruction. -/
theorem Pending.scalar {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hvisitor : FullVisitor.Total visitor)
    (ctx : code.Context) (hlocals : ctx.locals = locals)
    (opcode : U8) (hscalar : opcode.val ∉ controlOpcodes)
    (hsize : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = opcode) :
    code.step visitor st.core data env ctx opcode v ⦃ r =>
      r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  rw [scalar_context visitor st.core data env ctx ⟨locals, p.ft.results⟩ opcode v hscalar hlocals]
  by_cases hhigh : 0x45 ≤ opcode.val
  · exact p.step_numeric visitor hvisitor v hsize opcode hbyte hhigh
  by_cases hmemory : 0x28 ≤ opcode.val ∧ opcode.val ≤ 0x3E
  · obtain ⟨operation, hm⟩ := memory_meaning_exists opcode hmemory.1 hmemory.2
    exact p.step_memory visitor v hsize hvisitor opcode operation hbyte hm
  by_cases h_nop : opcode = code.OP_NOP
  · rw [h_nop] at hbyte ⊢; exact p.step_nop visitor hvisitor v hsize hbyte
  by_cases h_unreachable : opcode = code.OP_UNREACHABLE
  · rw [h_unreachable] at hbyte ⊢; exact p.step_unreachable visitor hvisitor v hsize hbyte
  by_cases h_i32_const : opcode = code.OP_I32_CONST
  · rw [h_i32_const] at hbyte ⊢; exact p.step_i32Const visitor hvisitor v hsize hbyte
  by_cases h_i64_const : opcode = code.OP_I64_CONST
  · rw [h_i64_const] at hbyte ⊢; exact p.step_i64Const visitor hvisitor v hsize hbyte
  by_cases h_f32_const : opcode = code.OP_F32_CONST
  · rw [h_f32_const] at hbyte ⊢; exact p.step_f32Const visitor hvisitor v hsize hbyte
  by_cases h_f64_const : opcode = code.OP_F64_CONST
  · rw [h_f64_const] at hbyte ⊢; exact p.step_f64Const visitor hvisitor v hsize hbyte
  by_cases h_drop : opcode = code.OP_DROP
  · rw [h_drop] at hbyte ⊢; exact p.step_drop visitor hvisitor v hsize hbyte
  by_cases h_select : opcode = code.OP_SELECT
  · rw [h_select] at hbyte ⊢; exact p.step_select visitor hvisitor v hsize hbyte
  by_cases h_local_get : opcode = code.OP_LOCAL_GET
  · rw [h_local_get] at hbyte ⊢; exact p.step_local_get visitor v hsize hvisitor (by simpa [global_simps] using hbyte)
  by_cases h_local_set : opcode = code.OP_LOCAL_SET
  · rw [h_local_set] at hbyte ⊢; exact p.step_local_set visitor v hsize hvisitor (by simpa [global_simps] using hbyte)
  by_cases h_local_tee : opcode = code.OP_LOCAL_TEE
  · rw [h_local_tee] at hbyte ⊢; exact p.step_local_tee visitor v hsize hvisitor (by simpa [global_simps] using hbyte)
  by_cases h_global_get : opcode = code.OP_GLOBAL_GET
  · rw [h_global_get] at hbyte ⊢; exact p.step_global_get visitor v hsize hvisitor (by simpa [global_simps] using hbyte)
  by_cases h_global_set : opcode = code.OP_GLOBAL_SET
  · rw [h_global_set] at hbyte ⊢; exact p.step_global_set visitor v hsize hvisitor (by simpa [global_simps] using hbyte)
  by_cases h_memory_size : opcode = code.OP_MEMORY_SIZE
  · rw [h_memory_size] at hbyte ⊢; exact p.step_memory_size visitor v hsize hvisitor (by simpa [global_simps] using hbyte)
  by_cases h_memory_grow : opcode = code.OP_MEMORY_GROW
  · rw [h_memory_grow] at hbyte ⊢; exact p.step_memory_grow visitor v hsize hvisitor (by simpa [global_simps] using hbyte)
  have hreserved : (0x06 ≤ opcode.val ∧ opcode.val ≤ 0x0A) ∨
      (0x12 ≤ opcode.val ∧ opcode.val ≤ 0x19) ∨
      (0x1C ≤ opcode.val ∧ opcode.val ≤ 0x1F) ∨
      (0x25 ≤ opcode.val ∧ opcode.val ≤ 0x27) := by
    simp only [controlOpcodes, List.mem_cons, not_or] at hscalar
    simp only [global_simps] at *
    scalar_tac
  rw [code.step.reserved visitor st.core data env ⟨locals, p.ft.results⟩ opcode v hreserved]
  simp

end Itasca.MultiValue
