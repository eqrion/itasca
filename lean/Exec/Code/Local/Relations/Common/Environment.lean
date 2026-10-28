import Exec.Code.Local.Relations.Common.FunctionSlots
import Exec.Code.Local.Relations.Common.PrepareFunctions
/-! The actual scheduler environment callback constructs source type/signature
metadata and initializes every defined-function result slot. -/
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

@[step] theorem compiler_environment_ready_sequence {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (scheduler : runtime.compiler.CompileScheduler A)
    (env : Itasca.module.Env) (emptyTypes : scheduler.signatures.val = [])
    (emptySlots : scheduler.func_param_slots.val = []) (emptyFunctions : scheduler.functions.val = []) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready ops scheduler env ⦃ out =>
      ∀ config, out.1 = .Ok config →
        SignatureSequence out.2.signatures.val env.types.val ∧
        out.2.func_param_slots.val.map (fun word => word.val) = env.func_types.val.map (fun ty => signatureSlots ty.params.val) ∧
        out.2.functions.val = List.replicate env.func_type_indices.val.length none ⦄ := by
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready
  simp only [Itasca.module.Env.impl.func_type_indices, bind_ok]
  split
  · simp [runtime.compiler.Budget.reject]
  · simp only [Itasca.module.Env.impl.types, bind_ok]
    split
    · simp [runtime.compiler.Budget.reject]
    · step with capture_signatures_loop_frame ops law scheduler env 0#usize (.Ok ())
        (by simp) (by intro _; simp [emptyTypes, SignatureSequence])
        as ⟨signatures, words, completed, functions, tail, codeStart, budget, status, effect⟩
      cases status with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok unit =>
        cases unit
        obtain ⟨sequence, slotsSame, functionsSame⟩ := effect rfl
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair]
        step with capture_function_slots_loop ops law
          ⟨signatures, words, completed, functions, tail, codeStart, budget⟩ env 0#usize (.Ok ())
          (by simp) (by intro _; simp [slotsSame, emptySlots])
          as ⟨signatures1, words1, completed1, functions1, tail1, codeStart1, budget1, status1, effect1⟩
        cases status1 with
        | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok unit =>
          cases unit
          obtain ⟨sameSignatures, slotsExact, functionsSame1⟩ := effect1 rfl
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair]
          step with prepare_functions_loop ops law budget1 functions1 env 0#usize (.Ok ())
            (by simp) (by intro _; simp [functionsSame1, functionsSame, emptyFunctions])
            as ⟨functions2, budget2, status2, effect2⟩
          cases status2 with
          | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok unit =>
            cases unit
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
            intro config accepted
            refine ⟨?_, slotsExact, effect2 rfl⟩
            simpa only [sameSignatures] using sequence

end Itasca.Runtime.Code
