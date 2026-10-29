import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackGrowth
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem compiler_table_branch_growth {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (status, after)) :
    after.function.code.val.length ≤ before.function.code.val.length + 2 := by
  unfold runtime.compiler.control.FunctionCompiler.table_branch at accepted
  repeat' growth_control_step accepted using ops, law

end Itasca.Runtime.Compiler
