import Exec.Code.Body.Reader.Table.ReaderTablePost
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem reader_table_decoded_wasm2 {V : Type} (visitor : code.OpVisitor V)
    {data env locals index st} (p : Wasm2.Pending data env .Wasm2 locals index st)
    (before after : V) (final : code.BodyState)
    (accepted : code.branch_table_with visitor st data env .Wasm2 before=.ok (.Ok (),final,after)) :
    ∃ depths fallback, BrTable.Decoded data st.core.pos depths fallback final.core.pos := by
  obtain ⟨unit,empty⟩ := code.branch_table_with.accepted_transfer visitor
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_accepts st data env before () final after _ accepted
  cases unit
  have erased : code.branch_table st data env .Wasm2 =.ok (.Ok (),final) := by
    simp only [code.branch_table,empty,bind_ok,uncurry_apply_pair]
  obtain ⟨C,outer,spine,header,base,typed,controls,blocks,values⟩ := p.opened
  have contextWf := Wasm2.Frames.enter_wf C
    (spine.context_wf (EnvTranslation.context_wf env ⟨locals,p.ft.results⟩)) p.current.form p.current.ins p.current.outs
  have labels := p.opened.branchLabels rfl C outer spine
  have effect := code.branch_table.prefix st data env .Wasm2 _ p.current.ctrl outer p.current.vals controls values base
    p.opened.shape.core _ contextWf _ p.current.ops typed labels
  rw [erased,WP.spec_ok] at effect
  obtain ⟨depths,fallback,decoded,_⟩ := effect rfl
  exact ⟨depths,fallback,decoded⟩
end Itasca.Runtime.Code
