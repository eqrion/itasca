import Exec.Code.Body.Reader.Table.ReaderTableDispatchWasm1
import Exec.Code.Body.Reader.Control.ReaderBranchWasm2
import Exec.Code.Body.Reader.Table.ReaderTableTargetsWasm2
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

theorem reader_table_post_wasm1 {V : Type} (visitor : code.OpVisitor V)
    {data env ctx bt st} (p : Wasm1.Pending data env ctx bt st)
    (before after : V) (final : code.OpIterState) (actual : U32) (common : code.BlockType)
    (depths : List U32) (fallback : U32) (next : Usize)
    (byte : data.val[p.start.val]'p.inbounds=code.OP_BR_TABLE)
    (encoded : BrTable.Decoded data st.pos depths fallback next)
    (accepted : code.read_br_table visitor st data before=.ok (.Ok (actual,common),final,after)) :
    ReaderPostWasm1 p final (BrTable.instruction depths fallback) true [] := by
  have erased := code.read_br_table.accepted_erasure visitor st data before (actual,common) final after accepted
  obtain ⟨C,outer,spine,header,base,typed,controls,values,contextWf,labels,returns⟩ :=
    p.opened.context (EnvTranslation.context_wf env ctx)
  have sourceLabels : (Wasm1.Frames.enter C p.current.form p.current.ctrl.block_type).LABELS=
      Control.labels st.ctrls.val := by simpa [EnvTranslation.context] using labels
  have effect := code.read_br_table.profile_prefix code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor st data ()
    _ p.current.ctrl outer p.current.vals controls values base _ contextWf p.current.ops typed sourceLabels
    (fun _ _ _ => ⟨.Ok (),(),rfl⟩)
  rw [erased,WP.spec_ok] at effect
  obtain ⟨actualDepths,decoded,finalValues,finalControls,sourceTyped,profile⟩ := effect actual common rfl
  obtain ⟨rfl,rfl,_⟩ := decoded.unique encoded
  have sourceAt : Wasm1.At data p.start (.plain (BrTable.instruction actualDepths actual)) final.pos :=
    .of_table_decoded actualDepths actual p.inbounds (by simpa [global_simps] using byte) p.pos decoded
  refine ⟨sourceAt,?_,?_⟩
  · exact ⟨C,outer,spine,⟨header.kind,header.prior,
      .simple header.emits (.plain _ (BrTable.instruction_wf _ _)),
      header.profile.append (.cons profile (.nil _)),header.priorProfile⟩,
      base,sourceTyped,finalControls,by change final.vals.val=outer++[]; simpa only [List.append_nil] using finalValues⟩
  · exact p.append_result C outer spine header base controls values final
      (BrTable.instruction actualDepths actual) true [] (BrTable.instruction_wf _ _) sourceAt sourceTyped finalControls
      (by simpa only [List.append_nil] using finalValues) (by simp) profile

theorem reader_table_post_wasm2 {V : Type} (visitor : code.OpVisitor V)
    {data env locals index st} (p : Wasm2.Pending data env locals index st)
    (before after : V) (final : code.BodyState) (depths : List U32) (fallback : U32) (next : Usize)
    (byte : data.val[p.start.val]'p.inbounds=0x0e#u8)
    (encoded : BrTable.Decoded data st.core.pos depths fallback next)
    (accepted : code.branch_table_with visitor st data env before=.ok (.Ok (),final,after)) :
    ReaderPostWasm2 p final.core (BrTable.instruction depths fallback) true [] := by
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
  obtain ⟨actualDepths,actual,decoded,finalValues,finalBlocks,finalControls,sourceTyped⟩ := effect rfl
  obtain ⟨rfl,rfl,_⟩ := decoded.unique encoded
  have sourceAt : Wasm1.At data p.start (.plain (BrTable.instruction actualDepths actual)) final.core.pos :=
    .of_table_decoded actualDepths actual p.inbounds byte p.pos decoded
  apply reader_append_context_wasm2 p C outer spine header base final.core
    (BrTable.instruction actualDepths actual) true [] (BrTable.instruction_wf _ _) (.plain sourceAt) sourceTyped finalControls
  · simpa only [finalBlocks] using blocks
  · simpa only [List.append_nil] using finalValues
  · exact sourceAt.declared _
end Exec.Code
