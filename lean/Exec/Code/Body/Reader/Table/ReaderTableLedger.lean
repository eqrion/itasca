import Exec.Code.Local.Callbacks.Table.FixupTablePreservation
import Exec.Code.Body.Relations.Table.BranchTableTables
import Exec.Code.Local.Capacity.AuxiliaryGrowth
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem compiler_br_table_auxiliary_growth {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : code.OpIterState) (fallback : U32) (types : signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state fallback types = .ok (.Ok (),after)) : AuxiliaryGrowth before after := by
  obtain ⟨targets,tables⟩ := compiler_br_table_tables ops law before after state fallback types accepted
  have counts := congrArg (fun t : CompilerTables => (t.indirect.length,t.simd.length,t.constants.length)) tables
  simp only [CompilerTables.ofFunction,CompilerTables.append,List.append_nil,Prod.mk.injEq] at counts
  have growth : before.function.code.val.length ≤ after.function.code.val.length := by
    by_cases live : before.reachable = true
    · obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,bound⟩ :=
        compiler_br_table_production ops law before after state fallback types live accepted
      omega
    · obtain ⟨_,code,_⟩ := compiler_br_table_dead_effect ops law before after state fallback types
        (Bool.eq_false_iff.mpr live) accepted
      simp [code]
  unfold AuxiliaryGrowth
  omega

theorem reader_table_ledger_wasm1 {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st final : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (budget : FixupBudget before.frames.val before.function.code.val.length)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_BR_TABLE before = .ok (.Ok (),final,after)) :
    AuxiliaryGrowth before after ∧ FixupBudget after.frames.val after.function.code.val.length := by
  obtain ⟨depth,common,collected,read,callback⟩ := reader_table_dispatch_wasm1
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st final data env ctx before after accepted
  obtain ⟨_,_,_,_,_,allocation,buffer,_,_,_,_,rfl,_⟩ :=
    compiler_read_br_table_wasm1 ops law before collected st final data depth common read
  exact ⟨compiler_br_table_auxiliary_growth ops law {before with budget := allocation, table_depths := buffer} after final depth (Control.resultView common) callback,
    compiler_br_table_fixup_budget ops law {before with budget := allocation, table_depths := buffer} after final depth (Control.resultView common) budget callback⟩

theorem reader_table_ledger_wasm2 {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st final : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (budget : FixupBudget before.frames.val before.function.code.val.length)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 14#u8 before = .ok (.Ok (),final,after)) :
    AuxiliaryGrowth before after ∧ FixupBudget after.frames.val after.function.code.val.length := by
  rw [Wasm2.CallbackTrace.dispatch_br_table] at accepted
  obtain ⟨_,_,_,_,_,fallback,types,_,_,allocation,buffer,_,_,_,_,_,_,_,callback⟩ :=
    compiler_read_br_table_wasm2 ops law before after st final data env accepted
  exact ⟨compiler_br_table_auxiliary_growth ops law {before with budget := allocation, table_depths := buffer} after final.core fallback types callback,
    compiler_br_table_fixup_budget ops law {before with budget := allocation, table_depths := buffer} after final.core fallback types budget callback⟩
end Exec.Code
