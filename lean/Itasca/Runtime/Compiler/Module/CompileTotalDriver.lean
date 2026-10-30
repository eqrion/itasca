import Itasca.Runtime.Compiler.Module.SchedulerSubmissionSafety
import Itasca.Runtime.Compiler.Module.Stream
import Itasca.Stream.InvariantDriver
import Itasca.Runtime.Compiler.Module.CompileStreamSource
import Itasca.Runtime.Compiler.Module.InitializerSourceTotal
import Itasca.Runtime.Compiler.Module.CompilerLargeEnvironment

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
open runtime.compiler

/-- Common driver assembly from the reached streaming phase. This internal
adapter derives source initializer space and all result/error bookkeeping. -/
theorem compile_with_total_of_streaming {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bytes : Slice U8) (profile : ValidationProfile)
    (limits : CompileLimits)
    (streaming : ∀ (codeStart codeEnd : Usize) (storage : metadata.Env),
      codeStart.val ≤ codeEnd.val ∧ codeEnd.val ≤ bytes.length →
      stream.validate_streaming CompileSource.Insts.ItascaStreamSource
        (CompileScheduler.Insts.ItascaStreamStreamingVisitor ops) 0#u64 profile
        {bytes,code_start := codeStart,code_end := codeEnd}
        (initialScheduler A limits codeStart) storage ⦃ out =>
          out.1 = .Ok () → SchedulerReady out.2.2 out.2.2.func_type_indices.val.length out.2.1 ⦄) :
    runtime.compiler.compile_with ops bytes profile limits ⦃ _ => True ⦄ := by
  unfold runtime.compiler.compile_with
  dsimp only
  split
  · simp
  · obtain ⟨⟨codeStart,codeEnd⟩,region,bounds⟩ := WP.spec_imp_exists (code_region_spec bytes)
    obtain ⟨storage,initialized,_⟩ := WP.spec_imp_exists metadata.Env.new.spec
    simp only [region,initialized,bind_ok,uncurry_apply_pair]
    obtain ⟨⟨status,scheduler,env⟩,validated,ready⟩ := WP.spec_imp_exists (streaming codeStart codeEnd storage bounds)
    simp only [initialScheduler] at validated
    simp only [validated]
    simp only [bind_ok,uncurry_apply_pair]
    cases status with
    | Err error => cases scheduler.budget.error <;> simp
    | Ok acceptedUnit =>
      cases acceptedUnit
      have held := ready rfl
      cases tailReady : scheduler.tail with
      | none => simp [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | some tail =>
        obtain ⟨raw,encoding,matched,_,bounded⟩ := compiler_stream_source ops law bytes profile limits
          codeStart codeEnd storage env scheduler tail bounds tailReady validated
        simp only [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
        obtain ⟨⟨collected,budget,pending⟩,collect,order⟩ := WP.spec_imp_exists
          (collect_functions_spec ops law scheduler.budget scheduler.functions)
        rw [collect]
        simp only [bind_ok,uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch]
        cases collected with
        | Err error => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok functions =>
          have count : functions.val.length = env.func_type_indices.val.length := by
            have eq := congrArg List.length (order functions rfl)
            simp only [List.length_map] at eq
            exact eq.symm.trans held.functions
          obtain ⟨⟨result,executable,finalBudget⟩,lowered,_⟩ := WP.spec_imp_exists
            (initializer_lower_source_total ops law env tail profile functions budget encoding matched bounded count)
          simp only [bind_ok]
          simp only [uninitializedModule] at lowered
          rw [lowered]
          cases result <;> cases choice : finalBudget.error <;> simp [choice]

end Itasca.Runtime.Compiler
