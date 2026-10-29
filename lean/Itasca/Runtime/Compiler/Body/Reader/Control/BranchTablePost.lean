import Itasca.Runtime.Compiler.Body.Reader.Control.BranchWasm2
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchTableTargetsWasm2
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchTableSuffix
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableOperands

/-!
The postcondition of a br_table reader step.

Main declarations: `reader_table_post_wasm2`. A direct consumer is `Compiler.Body.Reader.Control.BranchTableIndexed`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

theorem reader_table_post_wasm2 {V : Type} (visitor : code.OpVisitor V)
    {data env locals index st} (p : Wasm2.Pending data env .Wasm2 locals index st)
    (before after : V) (final : code.BodyState) (depths : List U32) (fallback : U32) (next : Usize)
    (byte : data.val[p.start.val]'p.inbounds=0x0e#u8)
    (encoded : BrTable.Decoded data st.core.pos depths fallback next)
    (accepted : code.branch_table_with visitor st data env .Wasm2 before=.ok (.Ok (),final,after)) :
    Wasm2.ReaderPost p final.core (BrTable.instruction depths fallback) true [] := by
  obtain ⟨unit,empty⟩ := code.branch_table_with.accepted_transfer visitor
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_accepts st data env before () final after _ accepted
  cases unit
  have erased : code.branch_table st data env .Wasm2 =.ok (.Ok (),final) := by
    simp only [code.branch_table,empty,bind_ok,uncurry_apply_pair]
  have effect := p.branch_table_reader byte
  rw [erased, WP.spec_ok] at effect
  obtain ⟨actualDepths, actual, decoded, post⟩ := effect rfl
  obtain ⟨rfl, rfl, _⟩ := decoded.unique encoded
  exact post

end Itasca.Runtime.Compiler
