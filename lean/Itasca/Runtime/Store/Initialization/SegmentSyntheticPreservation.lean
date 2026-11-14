import Itasca.Runtime.Store.Initialization.SegmentLoop
import Itasca.Runtime.Store.Initialization.SegmentInstructionMetadata
import Itasca.Runtime.Store.Initialization.InitializerErrors
import Itasca.Runtime.Interp.Relations.SourceClosure

/-!
Sections, each formerly its own module: SegmentLoopPreservation, SegmentSyntheticPreservation.
-/

/-! ## SegmentLoopPreservation -/

section

/-!
Object metadata and shape preservation through the segment initialization loop. Totality and source correspondence remain separate to keep lightweight loop consumers independent of source simulation.
-/

/-! ## Segment Loop Metadata -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
open Itasca.Runtime.Interp

/-- The actual retained initialization loop terminates normally after finitely
many straight-line instructions. It can report only the segment range traps;
all code and constant-read metadata, and the platform, remain unchanged. -/
theorem segment_loop_object_metadata {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (platform : P) (exec : runtime.interp.Execution)
    (instIndex function : Usize) (inst : runtime.store.ModuleInst)
    (code : runtime.bytecode.CompiledFunction) (position : U32)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some code)
    (frames : exec.frames.val = [initializerFrame instIndex function position])
    (positionBound : position.val < code.code.length)
    (ready : SegmentCodeReady store inst code exec.slots.length) :
    runtime.interp.run_synthetic_loop memory hooks floats allocator store platform exec (.Ok ())
      ⦃ out => SegmentObjectMetadata view store out.1 ⦄ := by
  unfold runtime.interp.run_synthetic_loop
  apply loop.spec_decr_nat (fun state => segmentRemaining code state.2.2.1 state.2.2.2)
    (fun state => SegmentObjectMetadata view store state.1 ∧ SegmentAddressSpace store state.1 ∧ state.2.1 = platform ∧
      state.2.2.1.slots.length = exec.slots.length ∧ SegmentStatus state.2.2.2 ∧
      (state.2.2.1.frames.val = [] ∨ ∃ pc : U32,
        state.2.2.1.frames.val = [initializerFrame instIndex function pc] ∧ pc.val < code.code.length))
  · rintro ⟨current, host, machine, result⟩ ⟨objects, metadata, hostEq, slots, status, frameShape⟩
    dsimp only at objects metadata hostEq slots status frameShape ⊢
    subst host
    cases result with
    | Err error =>
      simp only [runtime.interp.run_synthetic_loop.body, core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, ite_self, WP.spec_ok]
      simpa only [WP.spec_ok] using objects
    | Ok unitValue =>
      cases unitValue
      rcases frameShape with empty | ⟨pc, currentFrames, pcBound⟩
      · rw [synthetic_body_done memory hooks floats allocator machine current platform empty]
        simpa only [WP.spec_ok] using objects
      · rw [synthetic_body_active memory hooks floats allocator machine current platform
          (by simp [alloc.vec.Vec.length, currentFrames])]
        have currentFound : current.instances.val[instIndex.val]? = some inst := by rw [metadata.instances]; exact found
        have currentReady : SegmentCodeReady current inst code machine.slots.length := by
          rw [slots]
          exact ready.transport metadata
        let instruction := code.code.val[pc.val]
        have fetched : code.code.val[pc.val]? = some instruction := List.getElem?_eq_getElem pcBound
        have safe := segment_instruction_total memory hooks floats allocator view laws machine current platform
          instIndex function pc inst code instruction currentFound functionFound currentFrames fetched
          (lt_trans pcBound ready.size) (currentReady.instructions instruction (List.mem_of_getElem? fetched))
        have typed := segment_instruction_object_metadata memory hooks floats allocator view laws machine current platform
          instIndex function pc inst code instruction currentFound functionFound currentFrames fetched
          (lt_trans pcBound ready.size) (currentReady.instructions instruction (List.mem_of_getElem? fetched))
        step with segment_specs_and safe typed as ⟨result, next, after, host, effect, newObjects⟩
        have nextObjects := objects.trans newObjects
        have nextMetadata := metadata.trans effect.metadata
        have nextSlots := effect.slots.trans slots
        have nextHost := effect.platform
        dsimp only at nextHost nextSlots nextMetadata nextObjects
        subst host
        have nextFrames := effect.frames
        cases returns : segmentReturns code.code.val[pc.val] with
        | true =>
          simp only [returns, ↓reduceIte] at nextFrames
          refine ⟨nextObjects, nextMetadata, rfl, nextSlots, effect.status, Or.inl nextFrames, ?_⟩
          cases result <;> simp [segmentRemaining, nextFrames, currentFrames, initializerFrame]
        | false =>
          simp only [returns, Bool.false_eq_true, ↓reduceIte] at nextFrames
          obtain ⟨nextPc, nextValue, nextFrames⟩ := nextFrames
          have nextBound : nextPc.val < code.code.length := by
            have := ready.next_bound fetched returns
            omega
          refine ⟨nextObjects, nextMetadata, rfl, nextSlots, effect.status, Or.inr ⟨nextPc, nextFrames, nextBound⟩, ?_⟩
          cases result <;> simp only [segmentRemaining, nextFrames, currentFrames, initializerFrame]
          all_goals omega
  · exact ⟨.refl _ _, .refl store, rfl, rfl, Or.inl rfl, Or.inr ⟨position, frames, positionBound⟩⟩

end Itasca.Runtime.Store

end

/-! ## Segment Loop Shape -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
open Itasca.Runtime.Interp

/-- The actual retained initialization loop terminates normally after finitely
many straight-line instructions. It can report only the segment range traps;
all code and constant-read metadata, and the platform, remain unchanged. -/
theorem segment_loop_shape {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (platform : P) (exec : runtime.interp.Execution)
    (instIndex function : Usize) (inst : runtime.store.ModuleInst)
    (code : runtime.bytecode.CompiledFunction) (position : U32)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some code)
    (frames : exec.frames.val = [initializerFrame instIndex function position])
    (positionBound : position.val < code.code.length)
    (ready : SegmentCodeReady store inst code exec.slots.length)
    (shape : Shape view store)
    (compatible : ∀ instruction ∈ code.code.val, SegmentBulkCompatible store inst code instruction) :
    runtime.interp.run_synthetic_loop memory hooks floats allocator store platform exec (.Ok ())
      ⦃ out => Shape view out.1 ∧ SegmentTypes store out.1 ⦄ := by
  unfold runtime.interp.run_synthetic_loop
  apply loop.spec_decr_nat (fun state => segmentRemaining code state.2.2.1 state.2.2.2)
    (fun state => Shape view state.1 ∧ SegmentTypes store state.1 ∧ SegmentAddressSpace store state.1 ∧ state.2.1 = platform ∧
      state.2.2.1.slots.length = exec.slots.length ∧ SegmentStatus state.2.2.2 ∧
      (state.2.2.1.frames.val = [] ∨ ∃ pc : U32,
        state.2.2.1.frames.val = [initializerFrame instIndex function pc] ∧ pc.val < code.code.length))
  · rintro ⟨current, host, machine, result⟩ ⟨currentShape, types, metadata, hostEq, slots, status, frameShape⟩
    dsimp only at currentShape types metadata hostEq slots status frameShape ⊢
    subst host
    cases result with
    | Err error =>
      simp only [runtime.interp.run_synthetic_loop.body, core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, ite_self, WP.spec_ok]
      exact ⟨currentShape, types⟩
    | Ok unitValue =>
      cases unitValue
      rcases frameShape with empty | ⟨pc, currentFrames, pcBound⟩
      · rw [synthetic_body_done memory hooks floats allocator machine current platform empty]
        exact ⟨currentShape, types⟩
      · rw [synthetic_body_active memory hooks floats allocator machine current platform
          (by simp [alloc.vec.Vec.length, currentFrames])]
        have currentFound : current.instances.val[instIndex.val]? = some inst := by rw [metadata.instances]; exact found
        have currentReady : SegmentCodeReady current inst code machine.slots.length := by
          rw [slots]
          exact ready.transport metadata
        let instruction := code.code.val[pc.val]
        have fetched : code.code.val[pc.val]? = some instruction := List.getElem?_eq_getElem pcBound
        have safe := segment_instruction_total memory hooks floats allocator view laws machine current platform
          instIndex function pc inst code instruction currentFound functionFound currentFrames fetched
          (lt_trans pcBound ready.size) (currentReady.instructions instruction (List.mem_of_getElem? fetched))
        have typed := segment_instruction_shape memory hooks floats allocator view laws machine current platform
          instIndex function pc inst code instruction currentFound functionFound currentFrames fetched
          (lt_trans pcBound ready.size) (currentReady.instructions instruction (List.mem_of_getElem? fetched))
          ((compatible instruction (List.mem_of_getElem? fetched)).transport types) currentShape
        step with segment_specs_and safe typed as ⟨result, next, after, host, effect, nextShape, newTypes⟩
        have nextTypes := types.trans newTypes
        have nextMetadata := metadata.trans effect.metadata
        have nextSlots := effect.slots.trans slots
        have nextHost := effect.platform
        dsimp only at nextHost nextSlots nextMetadata nextShape nextTypes
        subst host
        have nextFrames := effect.frames
        cases returns : segmentReturns code.code.val[pc.val] with
        | true =>
          simp only [returns, ↓reduceIte] at nextFrames
          refine ⟨nextShape, nextTypes, nextMetadata, rfl, nextSlots, effect.status, Or.inl nextFrames, ?_⟩
          cases result <;> simp [segmentRemaining, nextFrames, currentFrames, initializerFrame]
        | false =>
          simp only [returns, Bool.false_eq_true, ↓reduceIte] at nextFrames
          obtain ⟨nextPc, nextValue, nextFrames⟩ := nextFrames
          have nextBound : nextPc.val < code.code.length := by
            have := ready.next_bound fetched returns
            omega
          refine ⟨nextShape, nextTypes, nextMetadata, rfl, nextSlots, effect.status, Or.inr ⟨nextPc, nextFrames, nextBound⟩, ?_⟩
          cases result <;> simp only [segmentRemaining, nextFrames, currentFrames, initializerFrame]
          all_goals omega
  · exact ⟨shape, .refl store, .refl store, rfl, rfl, Or.inl rfl, Or.inr ⟨position, frames, positionBound⟩⟩

end Itasca.Runtime.Store

end

end

/-! ## SegmentSyntheticPreservation -/

section

/-!
Synthetic initializer execution preserves object metadata and store shape. The totality and source-resource paths remain independent consumers of the lower loop.
-/

/-! ## Segment Synthetic Metadata -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
open Itasca.Runtime.Interp

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

end Itasca.Runtime.Store

end

/-! ## Segment Synthetic Shape -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
open Itasca.Runtime.Interp

/-- The actual synthetic entry point allocates its private slots/frame, then
runs the checked finite segment program. Allocation refusal and ordinary range
traps return normally; platform and address-space metadata are preserved. -/
theorem segment_synthetic_shape {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some code)
    (ready : SegmentCodeReady store inst code code.slot_count.val)
    (shape : Shape view store)
    (compatible : ∀ instruction ∈ code.code.val, SegmentBulkCompatible store inst code instruction) :
    runtime.interp.run_synthetic memory hooks floats allocator store platform instIndex function
      ⦃ out => Shape view out.2.1 ∧ SegmentTypes store out.2.1 ⦄ := by
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
    exact ⟨shape, .refl store⟩
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
      exact ⟨shape, .refl store⟩
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
      have typed := segment_loop_shape memory hooks floats allocator view laws store platform
        {prepared with frames := pushed} instIndex function inst code 0#u32 found functionFound pushedFrames
        (by simpa using nonempty) (by simpa only [capacity] using ready) shape compatible
      step with segment_specs_and total typed
        as ⟨after, host, finalSlots, result, metadata, hostEq, width, status, afterShape, types⟩
      subst host
      cases result with
      | Err error =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        exact ⟨afterShape, types⟩
      | Ok unitValue =>
        cases unitValue
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step with get_effect finalSlots.deref 0#usize
        step with get_effect finalSlots.deref 1#usize
        exact ⟨afterShape, types⟩

end Itasca.Runtime.Store

end

end
