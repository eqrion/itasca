import Itasca.Wasm2.Scalar.MemoryReader
import Itasca.Wasm2.Scalar.StackReader
import Itasca.Wasm2.Scalar.IndexReader
import Itasca.Wasm2.Scalar.NumericReader
import Itasca.Wasm2.Scalar.BasicReader
import Itasca.Wasm2.Scalar.Memory
import Itasca.Wasm2.Invariant
import Itasca.Wasm2.Step.ScalarContext
import Itasca.Binary.Wasm1.DeclaredReferences

/-!
# Scalar steps

`Pending` preservation for the shared `code.step` arms for non-control opcodes: `nop`,
`unreachable`, `drop`, `select`, constants, locals, globals, memory and numeric instructions.
`Pending.scalar` dispatches on the opcode and shows that a successful scalar step preserves the
typed zipper and appends exactly the independently decoded instruction.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

private theorem Pending.append_scalar {data env profile locals index st}
    (p : Pending data env profile locals index st)
    (C : context) (outer : List code.StackType)
    (spine : Frames.Spine env (bodyContext env locals p.ft) p.parents C outer p.current.form p.current.ins)
    (header : Frames.Header env C p.current)
    (base : p.current.ctrl.value_stack_base.val = outer.length)
    (_ctrls : st.core.ctrls.val = p.parents.map Frames.Saved.ctrl ++ [p.current.ctrl])
    (_vals : st.core.vals.val = outer ++ p.current.vals)
    (s : code.OpIterState) (op : instr) (poly : Bool) (newVals : List code.StackType)
    (hwf : wf_instr op) (encoded : Wasm1.At data p.start (.plain op) s.pos)
    (typed : TypedPrefix (Frames.enter C p.current.form p.current.ins p.current.outs)
      ((p.current.form.params p.current.ins).map Translate.valueType)
      (p.current.ops ++ [op]) poly newVals)
    (hc : s.ctrls.val = p.parents.map Frames.Saved.ctrl ++
      [{ p.current.ctrl with polymorphic_base := poly }])
    (hv : s.vals.val = outer ++ newVals)
    (_hlen : newVals.length ≤ p.current.vals.length + 1)
    (hbr : data.val[p.start.val]'p.inbounds ≠ 0x0E#u8) : p.After {st with core := s} := by
  have hb := p.opened
  obtain ⟨_, _, _, _, _, _, _, blocks, _⟩ := hb
  exact p.append_result C outer spine header base {st with core := s} op poly newVals hwf
    (At.plain encoded) typed hc (by simpa [hc, _ctrls] using blocks) hv
    (fun _ => ⟨encoded, encoded.leaf p.inbounds hbr _⟩) (encoded.declared _)


end Itasca.Wasm2

namespace Itasca.Wasm2


/-- NOP accepts arbitrary unread suffixes and records its opcode byte. -/
theorem Pending.step_nop {data env profile locals index st}
    (p : Pending data env profile locals index st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_NOP) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_NOP v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  apply WP.spec_mono (code.step_nop.total visitor st.core data env ⟨locals, p.ft.results⟩ v hvisitor.toCore)
  intro r hr _
  rw [hr]
  exact (p.nop_reader hbyte).after

/-- UNREACHABLE trims the current frame and records the exact byte. -/
theorem Pending.step_unreachable {data env profile locals index st}
    (p : Pending data env profile locals index st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_UNREACHABLE) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_UNREACHABLE v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  refine WP.spec_mono (code.step_unreachable.of_read visitor st.core data env ⟨locals, p.ft.results⟩ v
    (fun _ => True) (fun _ s => p.After {st with core := s}) ?_ hvisitor.toCore) ?_
  · apply WP.spec_mono (p.read_unreachable hbyte)
    intro r effect
    exact ⟨trivial, fun _ _ => effect.2.2.after⟩
  · intro r hr hok
    exact (hr.2 hok).choose_spec

/-- DROP covers concrete and polymorphic operands, and may reject an empty stack. -/
theorem Pending.step_drop {data env profile locals index st}
    (p : Pending data env profile locals index st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_DROP) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_DROP v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  refine WP.spec_mono (code.step_drop.of_read visitor st.core data env ⟨locals, p.ft.results⟩ v
    (fun _ => True) (fun _ s => p.After {st with core := s}) ?_ hvisitor.toCore) ?_
  · apply WP.spec_mono (p.read_drop hbyte)
    intro r effect
    refine ⟨trivial, ?_⟩
    intro value accepted
    obtain ⟨_, _, post⟩ := effect value accepted
    exact post.after
  · intro r effect accepted
    exact (effect.2 accepted).choose_spec

end Itasca.Wasm2

namespace Itasca.Wasm2


/-- The i32 constant step terminates on arbitrary immediate bytes and preserves the invariant on success. -/
theorem Pending.step_i32Const {data env profile locals index st}
    (p : Pending data env profile locals index st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V) (hsize : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_I32_CONST) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_I32_CONST v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  refine WP.spec_mono (code.step_i32_const.of_read visitor st.core data env ⟨locals, p.ft.results⟩ v
    (fun _ => True) (fun _ s => p.After {st with core := s}) ?_ hvisitor.toCore) ?_
  · apply WP.spec_mono (p.read_i32_const hsize hbyte)
    intro r effect
    exact ⟨trivial, fun value accepted => (effect value accepted).2.after⟩
  · intro r hr hok
    exact (hr.2 hok).choose_spec

/-- The i64 constant step terminates on arbitrary immediate bytes and preserves the invariant on success. -/
theorem Pending.step_i64Const {data env profile locals index st}
    (p : Pending data env profile locals index st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V) (hsize : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_I64_CONST) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_I64_CONST v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  refine WP.spec_mono (code.step_i64_const.of_read visitor st.core data env ⟨locals, p.ft.results⟩ v
    (fun _ => True) (fun _ s => p.After {st with core := s}) ?_ (hvisitor.on_i64_const v)) ?_
  · apply WP.spec_mono (p.read_i64_const hsize hbyte)
    intro r effect
    exact ⟨trivial, fun value accepted => (effect value accepted).2.after⟩
  · intro r hr hok
    exact (hr.2 hok).choose_spec

/-- The f32 constant step terminates on arbitrary immediate bytes and preserves the invariant on success. -/
theorem Pending.step_f32Const {data env profile locals index st}
    (p : Pending data env profile locals index st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V) (hsize : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_F32_CONST) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_F32_CONST v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  refine WP.spec_mono (code.step_f32_const.of_read visitor st.core data env ⟨locals, p.ft.results⟩ v
    (fun _ => True) (fun _ s => p.After {st with core := s}) ?_ (hvisitor.on_f32_const v)) ?_
  · apply WP.spec_mono (p.read_f32_const hsize hbyte)
    intro r effect
    exact ⟨trivial, fun value accepted => (effect value accepted).2.after⟩
  · intro r hr hok
    exact (hr.2 hok).choose_spec

/-- The f64 constant step terminates on arbitrary immediate bytes and preserves the invariant on success. -/
theorem Pending.step_f64Const {data env profile locals index st}
    (p : Pending data env profile locals index st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V) (hsize : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_F64_CONST) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_F64_CONST v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  refine WP.spec_mono (code.step_f64_const.of_read visitor st.core data env ⟨locals, p.ft.results⟩ v
    (fun _ => True) (fun _ s => p.After {st with core := s}) ?_ (hvisitor.on_f64_const v)) ?_
  · apply WP.spec_mono (p.read_f64_const hsize hbyte)
    intro r effect
    exact ⟨trivial, fun value accepted => (effect value accepted).2.after⟩
  · intro r hr hok
    exact (hr.2 hok).choose_spec

end Itasca.Wasm2

namespace Itasca.Wasm2


/-- Every numeric opcode extends the generated typing derivation under the current frame context. -/
theorem Pending.step_numeric_mapped {data env profile locals index st}
    (p : Pending data env profile locals index st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V) (hsize : st.core.vals.val.length < Usize.max) (opcode : U8) (op : Numeric.Operation)
    (hbyte : data.val[p.start.val]'p.inbounds = opcode)
    (hmap : Numeric.opcodeMeaning opcode = some op) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ opcode v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  have encoded : Wasm1.At data p.start (.plain op.instruction) st.core.pos :=
    .no_immediate p.inbounds hbyte p.pos (.numeric opcode op hmap)
  have effect := p.numeric_reader op st.core.pos hsize (.plain encoded) (encoded.declared _)
    (fun _ C => ⟨encoded, encoded.leaf p.inbounds
      (by rw [hbyte]; rintro rfl; simp [Numeric.opcodeMeaning] at hmap) C⟩)
  dsimp only at effect
  rw [code.step.numeric_dispatch visitor st.core data env ⟨locals,p.ft.results⟩ opcode v (Numeric.NumericOp.bounds hmap).1]
  rw [code.step_numeric.dispatch visitor st.core opcode op v hmap]
  apply WP.spec_mono (CoreVisitor.run.spec _ _ v (fun _ => True)
    (fun _ out => p.After {st with core := out}) ?_ (fun out _ => hvisitor.visit_numeric v out opcode))
  · intro result held accepted
    exact (held.2 accepted).choose_spec
  · apply WP.spec_mono effect
    intro result held
    refine ⟨trivial, ?_⟩
    intro unit accepted
    obtain ⟨_, _, post⟩ := held.2.2 unit accepted
    exact post.after

/-- Unmapped high opcodes terminate with rejection; mapped scalar opcodes preserve the invariant. -/
theorem Pending.step_numeric {data env profile locals index st}
    (p : Pending data env profile locals index st) {V : Type} (visitor : code.OpVisitor V)
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
theorem Pending.step_select {data env profile locals index st}
    (p : Pending data env profile locals index st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V) (hsize : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_SELECT) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_SELECT v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  rw [code.step_select.dispatch]
  refine WP.spec_mono (CoreVisitor.run.spec _ _ v (fun _ => True)
    (fun _ s => p.After {st with core := s}) ?_ (hvisitor.on_select v)) ?_
  · apply WP.spec_mono (p.read_select hsize hbyte)
    intro r effect
    refine ⟨trivial, ?_⟩
    intro value accepted
    obtain ⟨_, _, post⟩ := effect value accepted
    exact post.after
  · intro r effect accepted
    exact (effect.2 accepted).choose_spec

end Itasca.Wasm2

namespace Itasca.Wasm2


private theorem run_after {A V : Type} {data env profile locals index st}
    (p : Pending data env profile locals index st)
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

private theorem Pending.index_post_after {data env profile locals index st} (p : Pending data env profile locals index st)
    (C : context) (outer : List code.StackType)
    (spine : Frames.Spine env (bodyContext env locals p.ft) p.parents C outer p.current.form p.current.ins)
    (header : Frames.Header env C p.current)
    (base : p.current.ctrl.value_stack_base.val = outer.length)
    (ctrls : st.core.ctrls.val = p.parents.map Frames.Saved.ctrl ++ [p.current.ctrl])
    (vals : st.core.vals.val = outer ++ p.current.vals)
    (opcode : U8) (op : U32 → instr) (hbyte : data.val[p.start.val]'p.inbounds = opcode)
    (hwf : ∀ idx, wf_instr (op idx))
    (himm : ∀ idx bytes, Leb128.Encoding bytes idx.val → Wasm1.Immediate opcode (.plain (op idx)) bytes)
    (r : core.result.Result U32 error.OpError × code.OpIterState)
    (hpost : Scalar.IndexPost ((p.current.form.params p.current.ins).map Translate.valueType) data st.core outer p.current.vals
      (Frames.enter C p.current.form p.current.ins p.current.outs) p.current.ops op r)
    (idx : U32) (hr : r.1 = .Ok idx) (hbr : opcode ≠ 0x0E#u8 := by decide) :
    p.After {st with core := r.2} := by
  rcases r with ⟨result, out⟩
  dsimp only at hr
  subst result
  obtain ⟨_, _, _, _, _, _, _, blocks, _⟩ := p.opened
  obtain ⟨values, _, post⟩ := p.index_reader_post C outer spine header base ctrls blocks
    opcode op hbyte hwf himm out idx hpost hbr
  exact post.after

/-- `local.get` preserves `Pending` on success. -/
theorem Pending.step_local_get {data env profile locals index st} (p : Pending data env profile locals index st)
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
  refine WP.spec_mono (code.read_local_get.wasm2_prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    hsize _ hC p.current.ops (by simpa [hpoly] using typed)) ?_
  intro r hr idx hi
  exact p.index_post_after C outer spine header base ctrls vals 0x20#u8 _ hbyte
    (fun idx => .instr_case_43 _ (EnvTranslation.index_wf idx))
    (fun idx _ he => .localGet idx he) r hr idx hi

/-- `local.set` preserves `Pending` on success. -/
theorem Pending.step_local_set {data env profile locals index st} (p : Pending data env profile locals index st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hvisitor : FullVisitor.Total visitor)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x21#u8) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_LOCAL_SET v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hpoly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ⟨locals, p.ft.results⟩ (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (EnvTranslation.Matches.root env ⟨locals, p.ft.results⟩)).enter _
  rw [code.step_local_set.dispatch]
  apply run_after p _ _ v _ (hvisitor.on_local_set v)
  refine WP.spec_mono (code.read_local_set.wasm2_prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    (by simpa [Control.base, ctrls] using base) _ hC p.current.ops (by simpa [hpoly] using typed)) ?_
  intro r hr idx hi
  exact p.index_post_after C outer spine header base ctrls vals 0x21#u8 _ hbyte
    (fun idx => .instr_case_44 _ (EnvTranslation.index_wf idx))
    (fun idx _ he => .localSet idx he) r hr idx hi

/-- `local.tee` preserves `Pending` on success. -/
theorem Pending.step_local_tee {data env profile locals index st} (p : Pending data env profile locals index st)
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
  refine WP.spec_mono (code.read_local_tee.wasm2_prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    (by simpa [Control.base, ctrls] using base)
    hsize _ hC p.current.ops (by simpa [hpoly] using typed)) ?_
  intro r hr idx hi
  exact p.index_post_after C outer spine header base ctrls vals 0x22#u8 _ hbyte
    (fun idx => .instr_case_45 _ (EnvTranslation.index_wf idx))
    (fun idx _ he => .localTee idx he) r hr idx hi

/-- `global.get` preserves `Pending` on success. -/
theorem Pending.step_global_get {data env profile locals index st} (p : Pending data env profile locals index st)
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
  refine WP.spec_mono (code.read_global_get.wasm2_prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    hsize _ hC p.current.ops (by simpa [hpoly] using typed)) ?_
  intro r hr idx hi
  exact p.index_post_after C outer spine header base ctrls vals 0x23#u8 _ hbyte
    (fun idx => .instr_case_46 _ (EnvTranslation.index_wf idx))
    (fun idx _ he => .globalGet idx he) r hr idx hi

/-- `global.set` preserves `Pending` on success. -/
theorem Pending.step_global_set {data env profile locals index st} (p : Pending data env profile locals index st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hvisitor : FullVisitor.Total visitor)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x24#u8) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_GLOBAL_SET v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hpoly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ⟨locals, p.ft.results⟩ (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (EnvTranslation.Matches.root env ⟨locals, p.ft.results⟩)).enter _
  rw [code.step_global_set.dispatch]
  apply run_after p _ _ v _ (hvisitor.on_global_set v)
  refine WP.spec_mono (code.read_global_set.wasm2_prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    (by simpa [Control.base, ctrls] using base) _ hC p.current.ops (by simpa [hpoly] using typed)) ?_
  intro r hr idx hi
  exact p.index_post_after C outer spine header base ctrls vals 0x24#u8 _ hbyte
    (fun idx => .instr_case_47 _ (EnvTranslation.index_wf idx))
    (fun idx _ he => .globalSet idx he) r hr idx hi

private theorem Pending.reserved_post_after {data env profile locals index st} (p : Pending data env profile locals index st)
    (C : context) (outer : List code.StackType)
    (spine : Frames.Spine env (bodyContext env locals p.ft) p.parents C outer p.current.form p.current.ins)
    (header : Frames.Header env C p.current)
    (base : p.current.ctrl.value_stack_base.val = outer.length)
    (ctrls : st.core.ctrls.val = p.parents.map Frames.Saved.ctrl ++ [p.current.ctrl])
    (vals : st.core.vals.val = outer ++ p.current.vals)
    (opcode : U8) (op : instr) (hbyte : data.val[p.start.val]'p.inbounds = opcode)
    (hwf : wf_instr op) (himm : Wasm1.Immediate opcode (.plain op) [0#u8])
    (r : core.result.Result Unit error.OpError × code.OpIterState)
    (hpost : Scalar.ReservedPost ((p.current.form.params p.current.ins).map Translate.valueType) data st.core outer p.current.vals
      (Frames.enter C p.current.form p.current.ins p.current.outs) p.current.ops op r)
    (hr : r.1 = .Ok ()) (hbr : opcode ≠ 0x0E#u8 := by decide) :
    p.After {st with core := r.2} := by
  obtain ⟨⟨hp, hz, hn⟩, hc, rest, hv, hl, ht⟩ := hpost hr
  have hpoly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  apply p.append_scalar (hbr := by rw [hbyte]; exact hbr) C outer spine header base ctrls vals r.2 op
    p.current.ctrl.polymorphic_base rest hwf _ (by simpa [hpoly] using ht) _ hv hl
  · exact .of_immediate p.inbounds hbyte p.pos himm (.byte data st.core.pos r.2.pos 0#u8 hp hz hn)
  · simp [hc, ctrls]

/-- `memory.size` preserves `Pending` on success. -/
theorem Pending.step_memory_size {data env profile locals index st} (p : Pending data env profile locals index st)
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
  refine WP.spec_mono (code.read_memory_size.wasm2_prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    hsize _ hC p.current.ops (by simpa [hpoly] using typed)) ?_
  intro r hr u hi
  cases u
  exact p.reserved_post_after C outer spine header base ctrls vals 0x3F#u8 _ hbyte
    .instr_case_62 .memorySize r hr hi

/-- `memory.grow` preserves `Pending` on success. -/
theorem Pending.step_memory_grow {data env profile locals index st} (p : Pending data env profile locals index st)
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
  refine WP.spec_mono (code.read_memory_grow.wasm2_prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    (by simpa [Control.base, ctrls] using base) hsize
    _ hC p.current.ops (by simpa [hpoly] using typed)) ?_
  intro r hr u hi
  cases u
  exact p.reserved_post_after C outer spine header base ctrls vals 0x40#u8 _ hbyte
    .instr_case_63 .memoryGrow r hr hi

/-- Loads and stores preserve `Pending` on success. -/
theorem Pending.step_memory {data env profile locals index st} (p : Pending data env profile locals index st)
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
        exact code.read_load.wasm2_prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals hb
          hsize _ hC p.current.ops (by simpa [hpoly] using typed)
          opcode operation hrow hs
    | true =>
        simp only [↓reduceIte]
        exact code.read_store.wasm2_prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals hb
          _ hC p.current.ops (by simpa [hpoly] using typed) opcode operation hrow hs
  rw [code.step_memory.dispatch visitor st.core data env ⟨locals, p.ft.results⟩ v opcode operation hrow]
  apply run_after p _ _ v _ (fun s arg => hvisitor.visit_memory v s opcode arg)
  refine WP.spec_mono hread ?_
  intro r hr arg hi
  rcases r with ⟨result, out⟩
  dsimp only at hi
  subst result
  obtain ⟨values, post⟩ := p.memory_reader_post C outer spine header base ctrls blocks
    opcode operation hbyte hrow arg out hr
  exact post.after

end Itasca.Wasm2
namespace Itasca.Wasm2

/-- Successful shared scalar dispatch preserves the control zipper
and appends exactly the independently decoded instruction. -/
theorem Pending.scalar {data env profile locals index st} (p : Pending data env profile locals index st)
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
  · rw [h_nop] at hbyte ⊢; exact p.step_nop visitor hvisitor v hbyte
  by_cases h_unreachable : opcode = code.OP_UNREACHABLE
  · rw [h_unreachable] at hbyte ⊢; exact p.step_unreachable visitor hvisitor v hbyte
  by_cases h_i32_const : opcode = code.OP_I32_CONST
  · rw [h_i32_const] at hbyte ⊢; exact p.step_i32Const visitor hvisitor v hsize hbyte
  by_cases h_i64_const : opcode = code.OP_I64_CONST
  · rw [h_i64_const] at hbyte ⊢; exact p.step_i64Const visitor hvisitor v hsize hbyte
  by_cases h_f32_const : opcode = code.OP_F32_CONST
  · rw [h_f32_const] at hbyte ⊢; exact p.step_f32Const visitor hvisitor v hsize hbyte
  by_cases h_f64_const : opcode = code.OP_F64_CONST
  · rw [h_f64_const] at hbyte ⊢; exact p.step_f64Const visitor hvisitor v hsize hbyte
  by_cases h_drop : opcode = code.OP_DROP
  · rw [h_drop] at hbyte ⊢; exact p.step_drop visitor hvisitor v hbyte
  by_cases h_select : opcode = code.OP_SELECT
  · rw [h_select] at hbyte ⊢; exact p.step_select visitor hvisitor v hsize hbyte
  by_cases h_local_get : opcode = code.OP_LOCAL_GET
  · rw [h_local_get] at hbyte ⊢; exact p.step_local_get visitor v hsize hvisitor (by simpa [global_simps] using hbyte)
  by_cases h_local_set : opcode = code.OP_LOCAL_SET
  · rw [h_local_set] at hbyte ⊢; exact p.step_local_set visitor v hvisitor (by simpa [global_simps] using hbyte)
  by_cases h_local_tee : opcode = code.OP_LOCAL_TEE
  · rw [h_local_tee] at hbyte ⊢; exact p.step_local_tee visitor v hsize hvisitor (by simpa [global_simps] using hbyte)
  by_cases h_global_get : opcode = code.OP_GLOBAL_GET
  · rw [h_global_get] at hbyte ⊢; exact p.step_global_get visitor v hsize hvisitor (by simpa [global_simps] using hbyte)
  by_cases h_global_set : opcode = code.OP_GLOBAL_SET
  · rw [h_global_set] at hbyte ⊢; exact p.step_global_set visitor v hvisitor (by simpa [global_simps] using hbyte)
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

end Itasca.Wasm2
