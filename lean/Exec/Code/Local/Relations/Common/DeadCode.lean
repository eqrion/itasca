import Exec.Code.Local.Callbacks.Common.ObserveFrame
namespace Exec.Code
open Aeneas Aeneas.Std

theorem ObserveFrame.code {A : Type} {a b : runtime.compiler.FunctionCompiler A}
    (frame : ObserveFrame a b) : b.function.code = a.function.code := by rw [frame]

theorem ObserveFrame.reachable {A : Type} {a b : runtime.compiler.FunctionCompiler A}
    (frame : ObserveFrame a b) : b.reachable = a.reachable := by rw [frame]

set_option maxRecDepth 4096 in
/-- Every scalar opcode callback in a dead source region only observes the
validator state, preserving code, labels, immutable metadata and deadness. -/
@[step] theorem compiler_op_dead {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (dead : compiler.reachable = false) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state opcode a b bits ⦃ out =>
      ObserveFrame compiler out.2 ⦄ := by
  unfold runtime.compiler.lower.FunctionCompiler.op
  rw [if_neg (by simp [dead])]
  exact compiler_observe_frame ops law compiler state

@[step] theorem callback_return_dead {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (dead : compiler.reachable = false) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return ops compiler state ⦃ out =>
      ObserveFrame compiler out.2 ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return
  simp only [dead, Bool.false_eq_true, ite_false]
  exact compiler_observe_frame ops law compiler state

@[step] theorem callback_unreachable_dead {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (dead : compiler.reachable = false) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable ops compiler state ⦃ out =>
      ObserveFrame compiler out.2 ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable
  simp only [dead, Bool.false_eq_true, ite_false]
  exact compiler_observe_frame ops law compiler state
end Exec.Code
