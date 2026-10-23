import Exec.Store.Initialization.SegmentCodeReady

namespace Exec.Store
open Aeneas Aeneas.Std
open Exec.Interp

def segmentRemaining (code : runtime.bytecode.CompiledFunction) (exec : runtime.interp.Execution)
    (status : core.result.Result Unit runtime.ExecError) : Nat :=
  match status, exec.frames.val with
  | .Ok _, [frame] => code.code.length - frame.pc.val + 1
  | _, _ => 0

/-- The actual retained initialization loop terminates normally after finitely
many straight-line instructions. It can report only the segment range traps;
all code and constant-read metadata, and the platform, remain unchanged. -/
theorem segment_loop_total {M P F A : Type}
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
      ⦃ out => SegmentAddressSpace store out.1 ∧ out.2.1 = platform ∧
        out.2.2.1.length = exec.slots.length ∧ SegmentStatus out.2.2.2 ⦄ := by
  unfold runtime.interp.run_synthetic_loop
  apply loop.spec_decr_nat (fun state => segmentRemaining code state.2.2.1 state.2.2.2)
    (fun state => SegmentAddressSpace store state.1 ∧ state.2.1 = platform ∧
      state.2.2.1.slots.length = exec.slots.length ∧ SegmentStatus state.2.2.2 ∧
      (state.2.2.1.frames.val = [] ∨ ∃ pc : U32,
        state.2.2.1.frames.val = [initializerFrame instIndex function pc] ∧ pc.val < code.code.length))
  · rintro ⟨current, host, machine, result⟩ ⟨metadata, hostEq, slots, status, frameShape⟩
    dsimp only at metadata hostEq slots status frameShape ⊢
    subst host
    cases result with
    | Err error =>
      simp only [runtime.interp.run_synthetic_loop.body, core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, ite_self, WP.spec_ok]
      exact ⟨metadata, trivial, slots, status⟩
    | Ok unitValue =>
      cases unitValue
      rcases frameShape with empty | ⟨pc, currentFrames, pcBound⟩
      · rw [synthetic_body_done memory hooks floats allocator machine current platform empty]
        exact ⟨metadata, rfl, slots, status⟩
      · rw [synthetic_body_active memory hooks floats allocator machine current platform
          (by simp [alloc.vec.Vec.length, currentFrames])]
        have currentFound : current.instances.val[instIndex.val]? = some inst := by rw [metadata.instances]; exact found
        have currentReady : SegmentCodeReady current inst code machine.slots.length := by
          rw [slots]
          exact ready.transport metadata
        let instruction := code.code.val[pc.val]
        have fetched : code.code.val[pc.val]? = some instruction := List.getElem?_eq_getElem pcBound
        step with segment_instruction_total memory hooks floats allocator view laws machine current platform
          instIndex function pc inst code instruction currentFound functionFound currentFrames fetched
          (lt_trans pcBound ready.size) (currentReady.instructions instruction (List.mem_of_getElem? fetched))
          as ⟨result, next, after, host, effect⟩
        have nextMetadata := metadata.trans effect.metadata
        have nextSlots := effect.slots.trans slots
        have nextHost := effect.platform
        dsimp only at nextHost nextSlots nextMetadata
        subst host
        have nextFrames := effect.frames
        cases returns : segmentReturns code.code.val[pc.val] with
        | true =>
          simp only [returns, ↓reduceIte] at nextFrames
          refine ⟨nextMetadata, rfl, nextSlots, effect.status, Or.inl nextFrames, ?_⟩
          cases result <;> simp [segmentRemaining, nextFrames, currentFrames, initializerFrame]
        | false =>
          simp only [returns, Bool.false_eq_true, ↓reduceIte] at nextFrames
          obtain ⟨nextPc, nextValue, nextFrames⟩ := nextFrames
          have nextBound : nextPc.val < code.code.length := by
            have := ready.next_bound fetched returns
            omega
          refine ⟨nextMetadata, rfl, nextSlots, effect.status, Or.inr ⟨nextPc, nextFrames, nextBound⟩, ?_⟩
          cases result <;> simp only [segmentRemaining, nextFrames, currentFrames, initializerFrame]
          all_goals omega
  · exact ⟨.refl store, rfl, rfl, Or.inl rfl, Or.inr ⟨position, frames, positionBound⟩⟩

end Exec.Store
