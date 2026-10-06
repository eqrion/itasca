import Itasca.CompletenessFrame
import Itasca.CoreVisitor

open Aeneas Aeneas.Std

namespace Itasca.Completeness

theorem nop {st data env ctx C next front ins outs}
    (f : Frame st) (hb : Wasm.BytesAt data st.pos [] next)
    (hop : Instr_ok C .NOP (.mk_functype (.mk_list ins) (.mk_list outs)))
    (ht : Sequence.Realizes f.current.polymorphic_base f.operands (front ++ ins)) :
    StepResult f data env ctx 0x01#u8 next (front ++ outs) := by
  cases hop
  have he : next = st.pos := hb.empty
  subst next
  refine ⟨st, ?_, rfl, f.output_self ht, by omega⟩
  simp [code.step, global_simps, code.OpVisitor.on_nop.default, code.visit,
    core.result.Result.Insts.CoreOpsTry.branch]

theorem unreachable {st data env ctx C next front ins outs}
    (f : Frame st) (hb : Wasm.BytesAt data st.pos [] next)
    (_hop : Instr_ok C .UNREACHABLE (.mk_functype (.mk_list ins) (.mk_list outs))) :
    StepResult f data env ctx 0x00#u8 next (front ++ outs) := by
  have he : next = st.pos := hb.empty
  subst next
  obtain ⟨s, hr, hv, _, hc, hp⟩ := WP.spec_imp_exists
    (code.mark_unreachable.spec st f.parents f.current f.ctrls
      (by simp [f.base, f.vals]))
  have hv' : s.vals.val = f.outer := by simpa [f.vals, f.base] using hv
  refine ⟨s, ?_, hp, ⟨true, [], hc, by simpa using hv',
    Sequence.realizes_polymorphic_empty _⟩, ?_⟩
  · simp [code.step, global_simps, code.read_unreachable, hr,
      code.OpVisitor.on_unreachable.default, code.visit,
      core.result.Result.Insts.CoreOpsTry.branch]
  · simp only [hv', f.vals, List.length_append]
    omega

end Itasca.Completeness
