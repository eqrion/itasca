import Exec.Store.Invariant.CoreFunctionTables
import Exec.Store.Invariant.TypeStaging

namespace Exec.Store
open Aeneas Aeneas.Std

/-- An empty generic store has no defined-function certificate obligations. -/
theorem new_core_compiled {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (id : Usize) (limits : runtime.store.StoreLimits) (code : CodeInterpretation) :
    runtime.store.Store.with_identity memory id limits ⦃ store => Interp.CoreCompiledFunctions code store ⦄ := by
  simp [runtime.store.Store.with_identity, Interp.CoreCompiledFunctions]

/-- Defining a host function preserves all existing Wasm compiler certificates
on success and every allocation rejection. The new host entry has no Wasm body
and imposes no compiler-certificate obligation. -/
theorem define_host_core_compiled {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (store : runtime.store.Store M) (shape : Shape view store)
    (code : CodeInterpretation) (compiled : Interp.CoreCompiledFunctions code store)
    (ty : Itasca.types.FuncType) (identity : U64) :
    runtime.store.Store.define_host_with memory allocator store ty identity
      ⦃ out => Interp.CoreCompiledFunctions code out.2 ⦄ := by
  have objectBound : objectCount store ≤ Usize.max := by
    have bound := shape.object_count_bound
    scalar_tac
  unfold runtime.store.Store.define_host_with
  step with intern_type_effect memory allocator law store ty objectBound as ⟨status, interned, effect⟩
  have retained := effect.staged
  have sameFunctions := congrArg runtime.store.Store.funcs effect.only_types
  dsimp only at sameFunctions
  have unchangedCode : CodeAgreesOn store code code := by intro index inst found function; rfl
  have internedCompiled : Interp.CoreCompiledFunctions code interned := by
    intro function present
    rw [sameFunctions] at present
    exact core_function_compiled_prefix shape retained unchangedCode (compiled function present)
  cases status with
  | Err error =>
    simpa [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using internedCompiled
  | Ok signature =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with room_spec memory interned (effect.object_bound objectBound) as ⟨room, roomEq⟩
    rw [roomEq]
    by_cases space : objectCount interned < interned.limits.max_objects.val
    · simp only [if_pos space, bind_ok]
      obtain ⟨answer, reserveRun⟩ := reserve_wrapper_eq allocator law interned.funcs 1#usize
      rw [reserveRun]
      cases answer with
      | false =>
        simpa [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using internedCompiled
      | true =>
        simp only [↓reduceIte, bind_ok]
        have room : interned.funcs.length < Usize.max := by
          unfold objectCount at space
          scalar_tac
        step as ⟨functions, appended⟩
        have added : StagedPrefix interned {interned with funcs := functions} := by
          constructor <;> simp [appended]
        intro function present
        change function ∈ functions.val at present
        rw [appended, sameFunctions] at present
        rcases List.mem_append.mp present with old | host
        · exact core_function_compiled_prefix shape (retained.trans added) unchangedCode (compiled function old)
        · have same := List.mem_singleton.mp host
          subst function
          intro instanceIndex functionIndex defined
          simp at defined
    · simpa [if_neg space, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using internedCompiled

end Exec.Store
