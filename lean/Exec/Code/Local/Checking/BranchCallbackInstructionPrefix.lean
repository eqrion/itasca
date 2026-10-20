import Exec.Code.Local.Checking.NumericInstructionPrefix

namespace Exec.Code
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- Lift a source-derived raw branch preservation proof through actual br and
its final dead-stack observation. Forward/loop adapters discharge the local
branch premise; no body-level target trace is assumed here. -/
theorem compiler_br_callback_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (types : Itasca.signature.ResultType)
    (held : CompilerInstructionPrefix before)
    (branch : before.reachable = true → ∀ middle,
      runtime.compiler.control.FunctionCompiler.branch ops before depth 0#u32 false = .ok (.Ok (),middle) →
      CompilerInstructionPrefix middle)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br ops before state depth types = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br at called
  split at called
  · rename_i live
    obtain ⟨⟨status,middle⟩,emitted,rest⟩ := bind_ok_inv _ _ _ called
    cases status with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok unit =>
      cases unit
      simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
      have checked := branch live middle emitted
      apply compiler_observe_open_instructions ops law {middle with reachable := false} after state _ rest
      have owners : PendingInstructionSite {middle with reachable := false} = PendingInstructionSite middle := by
        funext index
        rfl
      simpa only [CompilerInstructionPrefix,owners] using checked
  · exact compiler_observe_open_instructions ops law before after state held called

/-- Lift source-derived conditional branch checking through actual br_if and
its stack observation, including a dead prefix that emits no branch. -/
theorem compiler_br_if_callback_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (types : Itasca.signature.ResultType)
    (held : CompilerInstructionPrefix before)
    (branch : before.reachable = true → ∀ middle,
      runtime.compiler.control.FunctionCompiler.branch ops before depth 1#u32 true = .ok (.Ok (),middle) →
      CompilerInstructionPrefix middle)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if ops before state depth types = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if at called
  split at called
  · rename_i live
    obtain ⟨⟨status,middle⟩,emitted,rest⟩ := bind_ok_inv _ _ _ called
    cases status with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok unit =>
      cases unit
      simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
      exact compiler_observe_open_instructions ops law middle after state (branch live middle emitted) rest
  · exact compiler_observe_open_instructions ops law before after state held called

/-- Every ordinary dead opcode performs only observation, regardless of its
immediates or numeric/reference/SIMD family. -/
theorem compiler_dead_op_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (dead : before.reachable = false) (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  unfold runtime.compiler.lower.FunctionCompiler.op at called
  rw [if_neg (by simp [dead])] at called
  exact compiler_observe_open_instructions ops law before after state held called

end Exec.Code
