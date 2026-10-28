import Itasca.Runtime.Code.Local.Callbacks.Control.FixupBranchPreservation
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

/-- ELSE either keeps the current fixup vector or appends one site while
emitting its corresponding skip jump. -/
theorem compiler_else_fixup_budget {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (budget : FixupBudget before.frames.val before.function.code.val.length)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else
      ops before state bt = .ok (.Ok (), after)) :
    FixupBudget after.frames.val after.function.code.val.length := by
  have growth := compiler_else_code_mono ops law before after state bt accepted
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else at accepted
  simp only [core.option.Option.take] at accepted
  repeat' paid_fixup_step accepted using ops, law
  all_goals try paid_fixup_effect accepted using ops, law
  all_goals fixup_close
  all_goals try exact budget.mono (by omega)
  all_goals
    apply (budget.mono (by omega)).set
    have selectedBudget := budget _ (by assumption)
    dsimp only
    try simp_all only [List.length_append, List.length_singleton]
    omega


end Itasca.Runtime.Code
