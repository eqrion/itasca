import Itasca.Runtime.Compiler.Body.Reader.Control.BranchWasm2
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchTableTargetsWasm2
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchTableSuffix
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableOperands

/-!
The postcondition of a br_table reader step.

Main declarations: `reader_table_post_wasm2`. A direct consumer is `Compiler.Body.Reader.Control.BranchTableIndexed`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

theorem reader_table_post_wasm2 {V : Type} (visitor : code.OpVisitor V)
    {data env locals index st} (p : Wasm2.Pending data env .Wasm2 locals index st)
    (before after : V) (final : code.BodyState) (depths : List U32) (fallback : U32) (next : Usize)
    (byte : data.val[p.start.val]'p.inbounds=0x0e#u8)
    (encoded : BrTable.Decoded data st.core.pos depths fallback next)
    (accepted : code.branch_table_with visitor st data env .Wasm2 before=.ok (.Ok (),final,after)) :
    ReaderPostWasm2 p final.core (BrTable.instruction depths fallback) true [] := by
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
  obtain ⟨actualDepths,actual,decoded,finalValues,finalBlocks,finalControls,sourceTyped,_⟩ := effect rfl
  obtain ⟨rfl,rfl,_⟩ := decoded.unique encoded
  have sourceAt : Wasm1.At data p.start (.plain (BrTable.instruction actualDepths actual)) final.core.pos :=
    .of_table_decoded actualDepths actual p.inbounds byte p.pos decoded
  apply reader_append_context_wasm2 p C outer spine header base final.core
    (BrTable.instruction actualDepths actual) true [] (BrTable.instruction_wf _ _) (.plain sourceAt) sourceTyped finalControls
  · simpa only [finalBlocks] using blocks
  · simpa only [List.append_nil] using finalValues
  · exact sourceAt.declared _
end Itasca.Runtime.Code
