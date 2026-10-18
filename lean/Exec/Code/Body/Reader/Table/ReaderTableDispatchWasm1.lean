import Exec.Code.Body.Reader.Table.ReaderTableInputsWasm1
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- The accepted instruction dispatch exposes the collecting reader and its
single terminal callback with the exact intermediate visitor state. -/
theorem reader_table_dispatch_wasm1 {V : Type} (visitor : code.OpVisitor V)
    (st final : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (before after : V)
    (accepted : code.step visitor st data env ctx code.OP_BR_TABLE before=.ok (.Ok (),final,after)) :
    ∃ depth common collected,
      code.read_br_table visitor st data before=.ok (.Ok (depth,common),final,collected) ∧
      visitor.on_br_table collected final depth (Control.resultView common)=.ok (.Ok (),after) := by
  rw [code.step_br_table.dispatch] at accepted
  obtain ⟨⟨result,state,collected⟩,read,rest⟩ := ResultFacts.bind_ok_inv _ _ _ accepted
  simp only [uncurry_apply_pair] at rest
  obtain ⟨⟨depth,common⟩,resultEq,callback⟩ := reader_run_success _ _ collected after final rest
  simp only [Result.ok.injEq,Prod.mk.injEq] at resultEq
  obtain ⟨rfl,rfl⟩ := resultEq
  exact ⟨depth,common,collected,read,callback⟩
end Exec.Code
