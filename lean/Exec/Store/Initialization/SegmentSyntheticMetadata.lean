import Exec.Store.Initialization.SegmentLoopMetadata
import Exec.Interp.Relations.Synthetic

namespace Exec.Store
open Aeneas Aeneas.Std
open Exec.Interp

/-- The actual synthetic entry point allocates its private slots/frame, then
runs the checked finite segment program. Allocation refusal and ordinary range
traps return normally; platform and address-space metadata are preserved. -/
theorem segment_synthetic_object_metadata {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some code)
    (ready : SegmentCodeReady store inst code code.slot_count.val) :
    runtime.interp.run_synthetic memory hooks floats allocator store platform instIndex function
      ⦃ out => SegmentObjectMetadata view store out.2.1 ⦄ := by
  unfold runtime.interp.run_synthetic
  step with vec_index_given store.instances instIndex inst found as ⟨actual, equal⟩
  subst actual
  step with vec_index_given inst.module.functions function code functionFound as ⟨actual, equal⟩
  subst actual
  simp only [lift, bind_ok, runtime.interp.Execution.new]
  step with ensure_effect allocator law _ _ _ as ⟨status, prepared, ensured⟩
  cases status with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    exact .refl _ _
  | Ok unitValue =>
    cases unitValue
    simp only [EnsureEffect] at ensured
    obtain ⟨limit, hslots, hother⟩ := ensured
    have slots : prepared.slots.val = List.replicate code.slot_count.val 0#u64 := by
      simpa [alloc.vec.Vec.new] using hslots
    have frames : prepared.frames.val = [] := by
      have h := congrArg runtime.interp.Execution.frames hother
      simpa [alloc.vec.Vec.new] using congrArg alloc.vec.Vec.val h
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨answer, reserved⟩ := law.reserve_eq prepared.frames 1#usize
    have reserveCall : runtime.reserve allocator prepared.frames 1#usize = .ok
        ((if answer then .Ok () else .Err (.Exhausted .Allocation)), prepared.frames) := by
      cases answer <;> simp [runtime.reserve, reserved]
    rw [reserveCall, bind_ok]
    cases answer with
    | false =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      exact .refl _ _
    | true =>
      simp only [↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step as ⟨pushed, hpushed⟩
      have pushedFrames : pushed.val = [initializerFrame instIndex function 0#u32] := by
        simpa [frames, initializerFrame] using hpushed
      have nonempty : 0 < code.code.length := by
        have := ready.returnLast
        by_contra empty
        have nil : code.code.val = [] := List.eq_nil_of_length_eq_zero (by simp only [alloc.vec.Vec.length] at empty; omega)
        simp [nil] at this
      have capacity : prepared.slots.length = code.slot_count.val := by simp [alloc.vec.Vec.length, slots]
      have total := segment_loop_total memory hooks floats allocator view laws store platform
        {prepared with frames := pushed} instIndex function inst code 0#u32 found functionFound pushedFrames
        (by simpa using nonempty) (by simpa only [capacity] using ready)
      have typed := segment_loop_object_metadata memory hooks floats allocator view laws store platform
        {prepared with frames := pushed} instIndex function inst code 0#u32 found functionFound pushedFrames
        (by simpa using nonempty) (by simpa only [capacity] using ready)
      step with segment_specs_and total typed
        as ⟨after, host, finalSlots, result, metadata, hostEq, width, status, objects⟩
      subst host
      cases result with
      | Err error =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        exact objects
      | Ok unitValue =>
        cases unitValue
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step with get_effect finalSlots.deref 0#usize
        step with get_effect finalSlots.deref 1#usize
        exact objects

end Exec.Store
