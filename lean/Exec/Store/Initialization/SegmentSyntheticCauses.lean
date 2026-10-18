import Exec.Store.Initialization.SegmentSyntheticSource
import Exec.Interp.Relations.SyntheticInitializerCauses

namespace Exec.Store
open Aeneas Aeneas.Std SpecExt
open Exec.Interp

/-- The actual synthetic segment entry point either refuses setup allocation
without changing the store, or follows the generated source reductions through
success or a range trap, retaining any earlier segment writes. -/
theorem segment_synthetic_source_causes {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize)
    (inst : runtime.store.Instance) (code : runtime.bytecode.CompiledFunction)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some code)
    (ready : SegmentCodeReady store inst code code.slot_count.val)
    (sourceCode : CodeInterpretation) (flow : Code.SegmentFlow 0 code.code.val)
    (compatible : ∀ instruction ∈ code.code.val, SegmentBulkCompatible store inst code instruction)
    (globals : ∀ index address value, .GlobalGet 0#u32 index ∈ code.code.val →
      inst.globals.val[index.val]? = some address → store.globals.val[address.index.val]? = some value → value.ty.valtype = .I32)
    (shape : Shape view store) (sourceSyntax : StoreSyntax sourceCode store) (bounds : SegmentBounds store)
    (ambient : frame) (ambientWf : wf_frame ambient) (moduleEq : ambient.MODULE = decodeInstance store inst) :
    runtime.interp.synthetic memory hooks floats allocator store platform instIndex function
      ⦃ out => (∃ reason, out.1 = .Err (.Exhausted reason) ∧ out.2.1 = store ∧
        SyntheticPreparationCause allocator store code (.Exhausted reason)) ∨
        SegmentExecutionStatus out.1 ∧ StepsH ⟨⟨decodeStore view sourceCode store,ambient⟩,Code.segmentSource code code.code.val⟩ []
          ⟨⟨decodeStore view sourceCode out.2.1,ambient⟩, match out.1 with | .Ok _ => [] | .Err _ => [.TRAP]⟩ ⦄ := by
  unfold runtime.interp.synthetic
  step with vec_index_given store.instances instIndex inst found as ⟨actual, equal⟩
  subst actual
  step with vec_index_given inst.module.functions function code functionFound as ⟨actual, equal⟩
  subst actual
  simp only [lift, bind_ok, runtime.interp.Execution.new]
  step with ensure_effect allocator law _ _ _ as ⟨status, prepared, ensured⟩
  cases status with
  | Err error =>
    have cause : SyntheticPreparationCause allocator store code error := by
      cases error <;> simp only [EnsureEffect] at ensured <;> try contradiction
      rename_i resource
      cases resource <;> simp only [EnsureEffect] at ensured <;> try contradiction
      · exact ensured.1
      · obtain ⟨within,needed,same,n,amount,refused⟩ := ensured
        have nEq : n = UScalar.cast .Usize code.slot_count := by
          apply UScalar.eq_of_val_eq
          simpa [alloc.vec.Vec.new,alloc.vec.Vec.length] using amount
        exact Or.inl (by simpa only [nEq] using refused)
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    left
    cases error <;> simp_all [EnsureEffect]
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
      have frameEq : prepared.frames = alloc.vec.Vec.new runtime.interp.Frame := alloc.vec.Vec.ext _ _ frames
      have cause : SyntheticPreparationCause allocator store code (.Exhausted .Allocation) :=
        Or.inr (by simpa only [frameEq] using reserved)
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,cause]
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
      have typed := segment_loop_source memory hooks floats allocator view laws sourceCode store platform
        {prepared with frames := pushed} instIndex function inst code 0#u32 0 found functionFound pushedFrames
        (by simpa using nonempty) (by simpa only [capacity] using ready)
        (by simpa using flow) compatible globals shape sourceSyntax bounds ambient ambientWf moduleEq
      step with segment_specs_and total typed
        as ⟨after, host, finalSlots, result, metadata, hostEq, width, status, objects⟩
      subst host
      cases result with
      | Err error =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        exact Or.inr ⟨by simpa [SegmentStatus,SegmentExecutionStatus] using status,
          by simpa [segmentState,segmentPending,vals,segmentResult] using objects⟩
      | Ok unitValue =>
        cases unitValue
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step with get_effect finalSlots.deref 0#usize
        step with get_effect finalSlots.deref 1#usize
        exact Or.inr ⟨trivial, by simpa [segmentState,segmentPending,vals,segmentResult] using objects⟩

end Exec.Store
