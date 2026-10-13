import Itasca.Wasm1.Invariant
import Itasca.Handler.BranchPrefix
import Itasca.Visitor.Total
import Itasca.Wasm1.BrTableProfile
import Itasca.Binary.Wasm1.BrTableLabels

open Aeneas Aeneas.Std

namespace Itasca.Wasm


theorem Pending.step_br {V : Type} {data env ctx bt st}
    (p : Pending data env ctx bt st) (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_BR) :
    code.step visitor st data env ctx code.OP_BR v ⦃ r => r.1 = .Ok () → p.After r.2.1 ⦄ := by
  simp only [code.OP_BR] at hbyte
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals, hC, labels, returns⟩ :=
    p.opened.context (EnvTranslation.context_wf env ctx)
  have hlabels : (WasmFrames.enter C p.current.form p.current.ctrl.block_type).LABELS =
      Control.labels st.ctrls.val := by simpa [EnvTranslation.context] using labels
  refine WP.spec_mono (code.step_br.of_read visitor st data env ctx v
    (fun _ => True) (fun _ s => p.After s) ?_ hvisitor.toCore) ?_
  · apply WP.spec_mono (code.read_br.prefix st data (p.parents.map WasmFrames.Saved.ctrl)
      p.current.ctrl outer p.current.vals ctrls vals base _ hC p.current.ops typed hlabels)
    intro r hr
    refine ⟨trivial, ?_⟩
    rintro ⟨d, resultBt⟩ hok
    obtain ⟨hd, hv, hc, ht⟩ := hr d resultBt hok
    apply p.append_result C outer spine header base ctrls vals r.2 (.BR (.mk_uN d.val)) true []
      (.instr_case_7 _ (Core.label_wf d))
      (.of_u32 d p.inbounds hbyte p.pos (fun _ => .br d) hd)
      ht hc (by simpa using hv) (by simp)
  · intro r hr hok
    exact (hr.2 hok).choose_spec

theorem Pending.step_brIf {V : Type} {data env ctx bt st}
    (p : Pending data env ctx bt st) (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_BR_IF) :
    code.step visitor st data env ctx code.OP_BR_IF v ⦃ r => r.1 = .Ok () → p.After r.2.1 ⦄ := by
  simp only [code.OP_BR_IF] at hbyte
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals, hC, labels, returns⟩ :=
    p.opened.context (EnvTranslation.context_wf env ctx)
  have hlabels : (WasmFrames.enter C p.current.form p.current.ctrl.block_type).LABELS =
      Control.labels st.ctrls.val := by simpa [EnvTranslation.context] using labels
  have hb : (Control.base st).val = outer.length := by simp [Control.base, ctrls, base]
  have hp : Control.polymorphic st = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic, ctrls]
  refine WP.spec_mono (code.step_br_if.of_read visitor st data env ctx v
    (fun _ => True) (fun _ s => p.After s) ?_ hvisitor.toCore) ?_
  · apply WP.spec_mono (code.read_br_if.prefix st data outer p.current.vals vals hb
      (by have := p.val_capacity; omega) _ hC p.current.ops (by simpa [hp] using typed) hlabels)
    intro r hr
    refine ⟨trivial, ?_⟩
    rintro ⟨d, resultBt⟩ hok
    obtain ⟨hd, hc, rest, hv, hlen, ht⟩ := hr d resultBt hok
    apply p.append_result C outer spine header base ctrls vals r.2 (.BR_IF (.mk_uN d.val))
      p.current.ctrl.polymorphic_base rest (.instr_case_8 _ (Core.label_wf d))
      (.of_u32 d p.inbounds hbyte p.pos (fun _ => .brIf d) hd)
      (by simpa [hp] using ht) _ hv hlen
    simpa [hc] using ctrls
  · intro r hr hok
    exact (hr.2 hok).choose_spec

theorem Pending.step_return {V : Type} {data env ctx bt st}
    (p : Pending data env ctx bt st) (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_RETURN) :
    code.step visitor st data env ctx code.OP_RETURN v ⦃ r => r.1 = .Ok () → p.After r.2.1 ⦄ := by
  simp only [code.OP_RETURN] at hbyte
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals, hC, labels, returns⟩ :=
    p.opened.context (EnvTranslation.context_wf env ctx)
  have hreturn : (WasmFrames.enter C p.current.form p.current.ctrl.block_type).RETURN =
      some (.mk_list (ctx.results.val.map Translate.valueType)) := by
    simpa [EnvTranslation.context] using returns
  refine WP.spec_mono (code.step_return.of_read visitor st data env ctx v
    (fun _ => True) (fun _ s => p.After s) ?_ hvisitor.toCore) ?_
  · apply WP.spec_mono (code.read_return.prefix st ctx (p.parents.map WasmFrames.Saved.ctrl)
      p.current.ctrl outer p.current.vals ctrls vals base _ hC p.current.ops typed hreturn)
    intro r hr
    refine ⟨trivial, ?_⟩
    intro u hok
    cases u
    obtain ⟨hv, hc, hp, ht⟩ := hr hok
    exact p.append_result C outer spine header base ctrls vals r.2 .RETURN true []
      .instr_case_12 (.no_immediate p.inbounds hbyte (by simpa [hp] using p.pos) .return_)
      ht hc (by simpa using hv) (by simp)
  · intro r hr hok
    exact (hr.2 hok).choose_spec

theorem Pending.step_brTable {V : Type} {data env ctx bt st}
    (p : Pending data env ctx bt st) (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_BR_TABLE) :
    code.step visitor st data env ctx code.OP_BR_TABLE v ⦃ r => r.1 = .Ok () → p.After r.2.1 ⦄ := by
  simp only [code.OP_BR_TABLE] at hbyte
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals, hC, labels, returns⟩ :=
    p.opened.context (EnvTranslation.context_wf env ctx)
  have hlabels : (WasmFrames.enter C p.current.form p.current.ctrl.block_type).LABELS =
      Control.labels st.ctrls.val := by simpa [EnvTranslation.context] using labels
  refine WP.spec_mono (code.step_br_table.of_read visitor st data env ctx v
    (fun _ s => p.After s) ?_ hvisitor.on_br_table) ?_
  · apply WP.spec_mono (code.read_br_table.profile_prefix visitor st data v (p.parents.map WasmFrames.Saved.ctrl)
      p.current.ctrl outer p.current.vals ctrls vals base _ hC p.current.ops typed hlabels
      hvisitor.on_br_table_label)
    intro r hr
    rintro ⟨d, resultBt⟩ hok
    obtain ⟨depths, hd, hv, hc, ht, hprofile⟩ := hr d resultBt hok
    exact p.append_result C outer spine header base ctrls vals r.2.1
      (BrTable.instruction depths d) true [] (BrTable.instruction_wf depths d)
      (.of_table_decoded depths d p.inbounds hbyte p.pos hd)
      ht hc (by simpa using hv) (by simp) hprofile
  · intro r hr hok
    exact (hr hok).choose_spec

end Itasca.Wasm
