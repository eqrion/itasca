import Itasca.Wasm2.Step.Dispatch

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- Exact factorization of bulk instruction callbacks around their readers. -/
def bulkStep {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : module.Env) (opcode : U32) (v : V) :
    Result (core.result.Result Unit error.OpError × code.OpIterState × V) :=
  match opcode with
  | 8#uscalar => CoreVisitor.run (code.read_memory_init st data env) (fun v s a => visitor.on_memory_init v s a) v
  | 9#uscalar => CoreVisitor.run (code.take_data_index st data env) (fun v s a => visitor.on_data_drop v s a) v
  | 10#uscalar => CoreVisitor.run (code.read_memory_copy st data env) (fun v s _ => visitor.on_memory_copy v s) v
  | 11#uscalar => CoreVisitor.run (code.read_memory_fill st data env) (fun v s _ => visitor.on_memory_fill v s) v
  | 12#uscalar => CoreVisitor.run (code.read_table_init st data env) (fun v s a => visitor.on_table_init v s a.1 a.2) v
  | 13#uscalar => CoreVisitor.run (code.take_element st data env) (fun v s a => visitor.on_elem_drop v s a.1) v
  | 14#uscalar => CoreVisitor.run (code.read_table_copy st data env) (fun v s a => visitor.on_table_copy v s a.1 a.2) v
  | 15#uscalar => CoreVisitor.run (code.read_table_grow st data env) (fun v s a => visitor.on_table_grow v s a) v
  | 16#uscalar => CoreVisitor.run (code.read_table_size st data env) (fun v s a => visitor.on_table_size v s a) v
  | 17#uscalar => CoreVisitor.run (code.read_table_fill st data env) (fun v s a => visitor.on_table_fill v s a) v
  | _ => .ok (.Err .UnrecognizedOpcode, st, v)

end Itasca.Wasm2

namespace Itasca

theorem code.step_bulk.eq_runs {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (opcode : U32) (v : V) :
    code.step_bulk visitor st data env opcode v = Wasm2.bulkStep visitor st data env opcode v := by
  unfold code.step_bulk Wasm2.bulkStep
  split <;> try rfl
  all_goals simp only [CoreVisitor.run]
  all_goals congr 1
  all_goals funext pair
  all_goals obtain ⟨r, s⟩ := pair
  all_goals cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  all_goals try (rename_i a; cases (show U32 × U32 from a))
  all_goals try (rename_i a; cases (show U32 × types.ValueType from a))
  all_goals try simp only [Std.uncurry]
  all_goals congr 1
  all_goals funext pair
  all_goals obtain ⟨reply, w⟩ := pair
  all_goals cases reply <;> simp [code.visit]

end Itasca
