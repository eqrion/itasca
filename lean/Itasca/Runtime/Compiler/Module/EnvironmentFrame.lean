import Itasca.Runtime.Compiler.Module.CompileSubmit
import Itasca.Stream.Scheduler
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
open Itasca Itasca.ResultFacts

def schedulerFrame {A : Type} (scheduler : runtime.compiler.CompileScheduler A) :=
  (scheduler.completed, scheduler.tail, scheduler.code_start)

theorem capture_signature_frame {A : Type} (allocator : runtime.platform.Alloc A)
    (before after : runtime.compiler.CompileScheduler A) (env : metadata.Env) (index : Usize)
    (result : core.result.Result Unit error.Error)
    (run : runtime.compiler.CompileScheduler.capture_signature allocator before env index = .ok (result, after)) :
    schedulerFrame after = schedulerFrame before := by
  unfold runtime.compiler.CompileScheduler.capture_signature at run
  obtain ⟨types, _, run⟩ := bind_ok_inv _ _ _ run
  obtain ⟨signature, _, run⟩ := bind_ok_inv _ _ _ run
  obtain ⟨params, _, run⟩ := bind_ok_inv _ _ _ run
  cases params with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
    exact congrArg schedulerFrame run.2.symm
  | Ok params =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at run
    obtain ⟨results, _, run⟩ := bind_ok_inv _ _ _ run
    cases results with
    | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
      exact congrArg schedulerFrame run.2.symm
    | Ok results =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at run
      obtain ⟨⟨status, budget, signatures⟩, _, run⟩ := bind_ok_inv _ _ _ run
      obtain ⟨_, _, run⟩ := bind_ok_inv _ _ _ run
      have same := congrArg Prod.snd (Result.ok_injective run)
      simpa [schedulerFrame] using congrArg schedulerFrame same.symm

theorem capture_func_slots_frame {A : Type} (allocator : runtime.platform.Alloc A)
    (before after : runtime.compiler.CompileScheduler A) (env : metadata.Env) (index : Usize)
    (result : core.result.Result Unit error.Error)
    (run : runtime.compiler.CompileScheduler.capture_func_slots allocator before env index = .ok (result, after)) :
    schedulerFrame after = schedulerFrame before := by
  unfold runtime.compiler.CompileScheduler.capture_func_slots at run
  obtain ⟨types, _, run⟩ := bind_ok_inv _ _ _ run
  obtain ⟨signature, _, run⟩ := bind_ok_inv _ _ _ run
  obtain ⟨params, _, run⟩ := bind_ok_inv _ _ _ run
  cases params with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
    exact congrArg schedulerFrame run.2.symm
  | Ok params =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at run
    obtain ⟨⟨status, budget, slots⟩, _, run⟩ := bind_ok_inv _ _ _ run
    obtain ⟨_, _, run⟩ := bind_ok_inv _ _ _ run
    have same := congrArg Prod.snd (Result.ok_injective run)
    simpa [schedulerFrame] using congrArg schedulerFrame same.symm

theorem environment_loop0_frame {A : Type} (allocator : runtime.platform.Alloc A)
    (before : runtime.compiler.CompileScheduler A) (env : metadata.Env) (index : Usize)
    (result : core.result.Result Unit error.Error) (output)
    (accepted : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0
      allocator before env index result = .ok output) :
    (output.2.2.1, output.2.2.2.2.1, output.2.2.2.2.2.1) = schedulerFrame before := by
  generalize measure : Usize.max - index.val = n
  induction n using Nat.strong_induction_on generalizing before index result with
  | h n ih =>
    unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0 at accepted
    rw [loop] at accepted
    simp only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0.body, Itasca.metadata.Env.impl.types, bind_ok] at accepted
    split at accepted
    · cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq] at accepted
        subst output
        rfl
      | Ok acceptedUnit =>
        cases acceptedUnit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte, Std.bind_assoc] at accepted
        obtain ⟨⟨nextResult, middle⟩, entry, tail⟩ := bind_ok_inv _ _ _ accepted
        simp only [uncurry_apply_pair, Std.bind_assoc, bind_ok] at tail
        obtain ⟨nextIndex, increment, tail⟩ := bind_ok_inv _ _ _ tail
        have arithmetic := UScalar.add_equiv index 1#usize
        rw [increment] at arithmetic
        have progress : nextIndex.val = index.val + 1 := by simpa using arithmetic.2.1
        have nextMax := nextIndex.hmax
        have smaller : Usize.max - nextIndex.val < n := by scalar_tac
        have tail' : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0
            allocator middle env nextIndex nextResult = .ok output := by
          simpa only [uncurry_apply_pair, bind_ok,
            runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0,
            runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0.body, Itasca.metadata.Env.impl.types, core.result.Result.is_ok] using tail
        exact (ih _ smaller middle nextIndex nextResult tail' rfl).trans
          (capture_signature_frame allocator before middle env index nextResult entry)
    · simp only [bind_ok, Result.ok.injEq] at accepted
      subst output
      rfl

theorem environment_loop1_frame {A : Type} (allocator : runtime.platform.Alloc A)
    (before : runtime.compiler.CompileScheduler A) (env : metadata.Env) (index : Usize)
    (result : core.result.Result Unit error.Error) (output)
    (accepted : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1
      allocator before env index result = .ok output) :
    (output.2.2.1, output.2.2.2.2.1, output.2.2.2.2.2.1) = schedulerFrame before := by
  generalize measure : Usize.max - index.val = n
  induction n using Nat.strong_induction_on generalizing before index result with
  | h n ih =>
    unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1 at accepted
    rw [loop] at accepted
    simp only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1.body, Itasca.metadata.Env.impl.func_types, bind_ok] at accepted
    split at accepted
    · cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq] at accepted
        subst output
        rfl
      | Ok acceptedUnit =>
        cases acceptedUnit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte, Std.bind_assoc] at accepted
        obtain ⟨⟨nextResult, middle⟩, entry, tail⟩ := bind_ok_inv _ _ _ accepted
        simp only [uncurry_apply_pair, Std.bind_assoc, bind_ok] at tail
        obtain ⟨nextIndex, increment, tail⟩ := bind_ok_inv _ _ _ tail
        have arithmetic := UScalar.add_equiv index 1#usize
        rw [increment] at arithmetic
        have progress : nextIndex.val = index.val + 1 := by simpa using arithmetic.2.1
        have nextMax := nextIndex.hmax
        have smaller : Usize.max - nextIndex.val < n := by scalar_tac
        have tail' : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1
            allocator middle env nextIndex nextResult = .ok output := by
          simpa only [uncurry_apply_pair, bind_ok,
            runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1,
            runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1.body, Itasca.metadata.Env.impl.func_types, core.result.Result.is_ok] using tail
        exact (ih _ smaller middle nextIndex nextResult tail' rfl).trans
          (capture_func_slots_frame allocator before middle env index nextResult entry)
    · simp only [bind_ok, Result.ok.injEq] at accepted
      subst output
      rfl

/-- Environment preparation does not alter queued workers, the source origin,
or the tail handoff. This statement follows from actual successful callbacks. -/
theorem compiler_environment_frame {A : Type} (allocator : runtime.platform.Alloc A)
    (before after : runtime.compiler.CompileScheduler A) (env : metadata.Env) (config : stream.Config)
    (accepted : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready
      allocator before env = .ok (.Ok config, after)) : schedulerFrame after = schedulerFrame before := by
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready at accepted
  simp only [Itasca.metadata.Env.impl.func_type_indices, bind_ok] at accepted
  split at accepted
  · simp [runtime.compiler.Budget.reject] at accepted
  · simp only [Itasca.metadata.Env.impl.types, bind_ok] at accepted
    split at accepted
    · simp [runtime.compiler.Budget.reject] at accepted
    · obtain ⟨⟨signatures, slots, completed, functions, tail, start, budget, status⟩, loop0, rest⟩ :=
        bind_ok_inv _ _ _ accepted
      have frame0 := environment_loop0_frame allocator before env 0#usize (.Ok ()) _ loop0
      cases status with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
      | Ok unit =>
        cases unit
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
        obtain ⟨⟨signatures1, slots1, completed1, functions1, tail1, start1, budget1, status1⟩, loop1, rest⟩ :=
          bind_ok_inv _ _ _ rest
        have frame1 := environment_loop1_frame allocator
          ⟨signatures, slots, completed, functions, tail, start, budget⟩ env 0#usize (.Ok ()) _ loop1
        cases status1 with
        | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
        | Ok unit =>
          cases unit
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
          obtain ⟨⟨functions2, budget2, status2⟩, _, rest⟩ := bind_ok_inv _ _ _ rest
          cases status2 with
          | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
          | Ok unit =>
            cases unit
            simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
              Result.ok.injEq, Prod.mk.injEq] at rest
            obtain ⟨_, output⟩ := rest
            subst after
            exact frame1.trans frame0
end Itasca.Runtime.Compiler
