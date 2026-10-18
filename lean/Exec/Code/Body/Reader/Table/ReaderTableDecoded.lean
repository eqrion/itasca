import Exec.Code.Body.Reader.Table.ReaderTablePost
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Accepted reading exposes independent binary decoding, including in dead
code. No compiler visitor totality or target-correctness premise is used. -/
theorem reader_table_decoded_wasm1 {V : Type} (visitor : code.OpVisitor V)
    {data env ctx bt st} (p : Wasm1.Pending data env ctx bt st)
    (before after : V) (final : code.OpIterState) (fallback : U32) (common : code.BlockType)
    (accepted : code.read_br_table visitor st data before=.ok (.Ok (fallback,common),final,after)) :
    ∃ depths, BrTable.Decoded data st.pos depths fallback final.pos := by
  have erased := code.read_br_table.accepted_erasure visitor st data before (fallback,common) final after accepted
  obtain ⟨C,outer,spine,header,base,typed,controls,values,contextWf,labels,returns⟩ :=
    p.opened.context (EnvTranslation.context_wf env ctx)
  have sourceLabels : (Wasm1.Frames.enter C p.current.form p.current.ctrl.block_type).LABELS=
      Control.labels st.ctrls.val := by simpa [EnvTranslation.context] using labels
  have effect := code.read_br_table.profile_prefix code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor st data ()
    _ p.current.ctrl outer p.current.vals controls values base _ contextWf p.current.ops typed sourceLabels
    (fun _ _ _ => ⟨.Ok (),(),rfl⟩)
  rw [erased,WP.spec_ok] at effect
  obtain ⟨depths,decoded,_⟩ := effect fallback common rfl
  exact ⟨depths,decoded⟩

theorem reader_table_decoded_wasm2 {V : Type} (visitor : code.OpVisitor V)
    {data env locals index st} (p : Wasm2.Pending data env locals index st)
    (before after : V) (final : code.BodyState)
    (accepted : code.branch_table_with visitor st data env before=.ok (.Ok (),final,after)) :
    ∃ depths fallback, BrTable.Decoded data st.core.pos depths fallback final.core.pos := by
  obtain ⟨unit,empty⟩ := code.branch_table_with.accepted_transfer visitor
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_accepts st data env before () final after accepted
  cases unit
  have erased : code.branch_table st data env=.ok (.Ok (),final) := by
    simp only [code.branch_table,empty,bind_ok,uncurry_apply_pair]
  obtain ⟨C,outer,spine,header,base,typed,controls,blocks,values⟩ := p.opened
  have contextWf := Wasm2.Frames.enter_wf C
    (spine.context_wf (EnvTranslation.context_wf env ⟨locals,p.ft.results⟩)) p.current.form p.current.ins p.current.outs
  have labels := p.opened.branchLabels rfl C outer spine
  have effect := code.branch_table.prefix st data env _ p.current.ctrl outer p.current.vals controls values base
    p.opened.shape.core _ contextWf _ p.current.ops typed labels
  rw [erased,WP.spec_ok] at effect
  obtain ⟨depths,fallback,decoded,_⟩ := effect rfl
  exact ⟨depths,fallback,decoded⟩
end Exec.Code
