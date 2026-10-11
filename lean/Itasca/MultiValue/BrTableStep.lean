import Itasca.MultiValue.BrTableComplete
import Itasca.MultiValue.BranchStep

open Aeneas Aeneas.Std

namespace Itasca.MultiValue

theorem Pending.branch_table {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x0E#u8) :
    multi_value.branch_table st data env ⦃ r => r.1 = .Ok () → p.After r.2 ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hC := Frames.enter_wf C (spine.context_wf (EnvTranslation.context_wf env ⟨locals, p.ft.results⟩))
    p.current.form p.current.ins p.current.outs
  have hl := p.opened.branchLabels rfl C outer spine
  apply WP.spec_mono (multi_value.branch_table.prefix st data env (p.parents.map Frames.Saved.ctrl)
    p.current.ctrl outer p.current.vals ctrls vals base p.opened.shape.core p.opened.shape.aligned
    _ hC _ p.current.ops typed hl)
  intro r hr hok
  obtain ⟨depths, default, hd, hv, hb, hc, ht⟩ := hr hok
  exact p.append_result C outer spine header base r.2 (BrTable.instruction depths default) true []
    (BrTable.instruction_wf depths default)
    (.plain (.of_table_decoded depths default p.inbounds hbyte p.pos hd)) ht hc
    (by simpa [hb] using blocks) (by simpa using hv)

end Itasca.MultiValue
