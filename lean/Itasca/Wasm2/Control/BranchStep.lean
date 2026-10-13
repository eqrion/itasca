import Itasca.Wasm2.Control.BranchComplete
import Itasca.Wasm2.Control.Call
import Itasca.Wasm2.Invariant
import Itasca.Wasm2.Control.BrTableComplete

/-!
# Branch, `br_table` and call steps

`Pending` preservation for the opcodes `call` (`0x10`), `call_indirect` (`0x11`), `br` (`0x0c`),
`br_if` (`0x0d`) and `br_table` (`0x0e`). Each of `Pending.call`, `Pending.call_indirect`,
`Pending.branch`, `Pending.branch_if` and `Pending.branch_table` combines the handler's prefix
theorem with `Pending.append_result`. `Frames.Open.branchLabels` supplies the label agreement they
all need.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- In a zipper whose root has no labels, the runtime labels agree with the context's. -/
theorem Frames.Open.branchLabels {env root st parents current}
    (h : Frames.Open env root st parents current) (hroot : root.LABELS = [])
    (C : context) (outer : List code.StackType)
    (spine : Frames.Spine env root parents C outer current.form current.ins) :
    BranchLabels env st (Frames.enter C current.form current.ins current.outs) := by
  intro depth view hl
  have hd : depth.val < st.blocks.val.length := by
    by_contra hn
    simp_all [labelAt]
  have he := Frames.Open.labels h depth.val
  obtain ⟨C', outer', spine', header, base, typed, ctrls, blocks, vals⟩ := h
  have hd' : depth.val < (Frames.labels (parents ++ [current])).length := by
    simpa [Frames.labels, blocks] using hd
  rw [hl] at he
  cases hr : resolve env view with
  | none => simp [hr, List.getElem?_eq_getElem hd'] at he
  | some ts =>
    refine ⟨ts, rfl, ?_⟩
    have hcontext : (Frames.enter C current.form current.ins current.outs).LABELS =
        Frames.labels (parents ++ [current]) := by
      simp [Frames.enter, Control.labelContext_labels, spine.labels, hroot, Frames.labels]
    simpa [hr, hcontext] using he.symm

/-- The direct `call` opcode (`0x10`) preserves `Pending` on success. -/
theorem Pending.call {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x10#u8) :
    code.call st data env false ⦃ r => r.1 = .Ok () → p.After r.2 ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hpoly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC := (spine.matches (EnvTranslation.Matches.root env ⟨locals, p.ft.results⟩)).enter
    (p.current.form.label p.current.ins p.current.outs)
  apply WP.spec_mono (code.call.direct_prefix st data env ⟨locals, p.ft.results⟩ outer
    p.current.vals vals (by simp [Control.base, ctrls, base]) _ hC _ p.current.ops
    (by simpa [hpoly, Frames.enter] using typed))
  intro r hr hok
  obtain ⟨idx, hd, hc, hb, rest, hv, ht⟩ := hr hok
  apply p.append_result C outer spine header base r.2 (.CALL (.mk_uN idx.val))
    p.current.ctrl.polymorphic_base rest (.instr_case_10 _ (EnvTranslation.index_wf idx))
    (.plain (.of_u32 idx p.inbounds hbyte p.pos (fun _ => .call idx) hd))
    (by simpa [hpoly, Frames.enter] using ht) _ (by simpa [hb] using blocks) hv
  simpa [hc] using ctrls

/-- The `call_indirect` opcode (`0x11`) preserves `Pending` on success. -/
theorem Pending.call_indirect {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x11#u8) :
    code.call st data env true ⦃ r => r.1 = .Ok () → p.After r.2 ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hpoly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC := (spine.matches (EnvTranslation.Matches.root env ⟨locals, p.ft.results⟩)).enter
    (p.current.form.label p.current.ins p.current.outs)
  apply WP.spec_mono (code.call.indirect_prefix st data env ⟨locals, p.ft.results⟩ outer
    p.current.vals vals (by simp [Control.base, ctrls, base]) _ hC _ p.current.ops
    (by simpa [hpoly, Frames.enter] using typed))
  intro r hr hok
  obtain ⟨idx, table, middle, hd, hdtable, hc, hb, rest, hv, ht⟩ := hr hok
  obtain ⟨typeBytes, hts, htl, htb, hte⟩ := hd
  obtain ⟨tableBytes, hss, hsl, hsb, hse⟩ := hdtable
  have hbytes := (Wasm1.BytesAt.mk hts htl htb).append (Wasm1.BytesAt.mk hss hsl hsb)
  apply p.append_result C outer spine header base r.2 (.CALL_INDIRECT (.mk_uN table.val) (.mk_uN idx.val))
    p.current.ctrl.polymorphic_base rest
    (.instr_case_11 _ _ (EnvTranslation.index_wf table) (EnvTranslation.index_wf idx))
    (.of_immediate p.inbounds hbyte p.pos (.reference (.callIndirect idx table hte hse)) hbytes)
    (by simpa [hpoly, Frames.enter] using ht) _ (by simpa [hb] using blocks) hv
  simpa [hc] using ctrls

/-- The `br` opcode (`0x0c`) preserves `Pending` on success. -/
theorem Pending.branch {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x0C#u8) :
    code.branch st data env false ⦃ r => r.1 = .Ok () → p.After r.2 ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hC := Frames.enter_wf C (spine.context_wf (EnvTranslation.context_wf env ⟨locals, p.ft.results⟩))
    p.current.form p.current.ins p.current.outs
  have hl := p.opened.branchLabels rfl C outer spine
  apply WP.spec_mono (code.branch.prefix st data env (p.parents.map Frames.Saved.ctrl)
    p.current.ctrl outer p.current.vals ctrls vals base p.opened.shape.aligned
    _ hC _ p.current.ops typed hl)
  intro r hr hok
  obtain ⟨depth, hd, hv, hb, hc, ht⟩ := hr hok
  exact p.append_result C outer spine header base r.2 (.BR (.mk_uN depth.val)) true []
    (.instr_case_7 _ (Spec.label_wf depth))
    (.plain (.of_u32 depth p.inbounds hbyte p.pos (fun _ => .br depth) hd)) ht hc
    (by simpa [hb] using blocks) (by simpa using hv)

/-- The `br_if` opcode (`0x0d`) preserves `Pending` on success. -/
theorem Pending.branch_if {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x0D#u8) :
    code.branch st data env true ⦃ r => r.1 = .Ok () → p.After r.2 ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hC := Frames.enter_wf C (spine.context_wf (EnvTranslation.context_wf env ⟨locals, p.ft.results⟩))
    p.current.form p.current.ins p.current.outs
  have hl := p.opened.branchLabels rfl C outer spine
  have hpoly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  apply WP.spec_mono (code.branch.conditional_prefix st data env outer p.current.vals vals
    (by simp [Control.base, ctrls, base]) p.opened.shape.core p.opened.shape.aligned
    _ hC _ p.current.ops (by simpa [hpoly, Frames.enter] using typed) hl)
  intro r hr hok
  obtain ⟨depth, hd, hc, hb, rest, hv, ht⟩ := hr hok
  apply p.append_result C outer spine header base r.2 (.BR_IF (.mk_uN depth.val))
    p.current.ctrl.polymorphic_base rest (.instr_case_8 _ (Spec.label_wf depth))
    (.plain (.of_u32 depth p.inbounds hbyte p.pos (fun _ => .brIf depth) hd))
    (by simpa [hpoly, Frames.enter] using ht) _ (by simpa [hb] using blocks) hv
  simpa [hc] using ctrls

end Itasca.Wasm2

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- The `br_table` opcode (`0x0e`) preserves `Pending` on success. -/
theorem Pending.branch_table {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x0E#u8) :
    code.branch_table st data env ⦃ r => r.1 = .Ok () → p.After r.2 ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hC := Frames.enter_wf C (spine.context_wf (EnvTranslation.context_wf env ⟨locals, p.ft.results⟩))
    p.current.form p.current.ins p.current.outs
  have hl := p.opened.branchLabels rfl C outer spine
  apply WP.spec_mono (code.branch_table.prefix st data env (p.parents.map Frames.Saved.ctrl)
    p.current.ctrl outer p.current.vals ctrls vals base p.opened.shape.core
    _ hC _ p.current.ops typed hl)
  intro r hr hok
  obtain ⟨depths, default, hd, hv, hb, hc, ht⟩ := hr hok
  exact p.append_result C outer spine header base r.2 (BrTable.instruction depths default) true []
    (BrTable.instruction_wf depths default)
    (.plain (.of_table_decoded depths default p.inbounds hbyte p.pos hd)) ht hc
    (by simpa [hb] using blocks) (by simpa using hv)
    (by simp [BrTable.instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices])

end Itasca.Wasm2
