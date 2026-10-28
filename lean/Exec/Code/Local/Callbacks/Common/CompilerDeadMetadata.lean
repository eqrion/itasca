import Exec.Code.Local.Callbacks.Common.CompilerOrdinaryResults
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Ordinary opcodes in an unreachable suffix only observe the validator.
In particular, they emit no code and preserve the structured-control frames. -/
theorem compiler_dead_op_frame {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (dead : compiler.reachable = false) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state opcode a b bits ⦃ out =>
      ObserveFrame compiler out.2 ⦄ := by
  unfold runtime.compiler.lower.FunctionCompiler.op
  rw [if_neg (by simp only [dead, Bool.false_eq_true, not_false_eq_true])]
  exact compiler_observe_frame ops law compiler state

theorem compiler_dead_op_fields {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (dead : compiler.reachable = false) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state opcode a b bits ⦃ out =>
      out.2.function.code = compiler.function.code ∧ out.2.frames = compiler.frames ∧
      out.2.function.locals = compiler.function.locals ∧ out.2.reachable = false ⦄ := by
  apply WP.spec_mono (compiler_dead_op_frame ops law compiler state opcode a b bits dead)
  intro out frame
  rw [frame]
  exact ⟨rfl, rfl, rfl, dead⟩
end Itasca.Runtime.Code
