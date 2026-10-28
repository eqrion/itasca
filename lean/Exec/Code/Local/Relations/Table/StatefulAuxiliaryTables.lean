import Exec.Code.Local.Callbacks.Table.CompilerAuxiliaryTables
import Exec.Code.Local.Relations.Common.StatefulLowering
import Exec.Code.Local.Relations.Calls.IndirectCallLowering
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
theorem compiler_stateful_auxiliary_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : Abs.Stateful.Instruction) (a b : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state (statefulOpcode op) a b 0#u128 = .ok (status, after)) :
    compilerAuxiliaryTables after.function = compilerAuxiliaryTables before.function := by
  by_cases reach : before.reachable = true
  · rw [lower_stateful_dispatch ops before state op a b reach] at accepted
    cases op <;> simp only [statefulLowering] at accepted
    all_goals repeat' auxiliary_tables_step accepted using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at accepted
    rw [if_neg reach] at accepted
    have tables := compiler_observe_tables ops law before after state status accepted
    simpa only [CompilerTables.ofFunction, CompilerTables.mk.injEq, compilerAuxiliaryTables] using
      congrArg (fun t : CompilerTables => (t.simd,t.constants,t.jumpTables)) tables
theorem compiler_indirect_call_auxiliary_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 17#u16 a b 0#u128 = .ok (status, after)) :
    compilerAuxiliaryTables after.function = compilerAuxiliaryTables before.function := by
  by_cases reach : before.reachable = true
  · rw [lower_indirect_call_dispatch ops before state a b reach] at accepted
    unfold indirectCallLowering at accepted
    repeat' auxiliary_tables_step accepted using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at accepted
    rw [if_neg reach] at accepted
    have tables := compiler_observe_tables ops law before after state status accepted
    simpa only [CompilerTables.ofFunction, CompilerTables.mk.injEq, compilerAuxiliaryTables] using
      congrArg (fun t : CompilerTables => (t.simd,t.constants,t.jumpTables)) tables
end Itasca.Runtime.Code
