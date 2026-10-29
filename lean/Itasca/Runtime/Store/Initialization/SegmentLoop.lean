import Itasca.Runtime.Store.Initialization.SegmentCertificate

/-!
Ready segment bytecode and total loop execution. Readiness transport and the next-instruction bound justify each iteration and the decreasing remaining-code measure.
-/

/-! ## Segment Code Ready -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- A finite straight-line initialization body. Every instruction carries only
syntactic bounds and issued-address facts, and the final instruction returns. -/
structure SegmentCodeReady {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction) (width : Nat) : Prop where
  size : code.code.length < U32.max
  returnLast : code.code.val.getLast? = some (.Return 0#u32 0#u32)
  instructions : ∀ instruction ∈ code.code.val, SegmentInstructionReady store inst code width instruction

theorem SegmentCodeReady.transport {M : Type} {store after : runtime.store.Store M}
    {inst code width} (ready : SegmentCodeReady store inst code width)
    (metadata : SegmentAddressSpace store after) : SegmentCodeReady after inst code width :=
  ⟨ready.size, ready.returnLast, fun instruction member => (ready.instructions instruction member).transport metadata⟩

theorem segment_program_ready {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (program : Code.SegmentProgram inst.module code)
    (pcBound : code.code.length < U32.max)
    (shape : InstanceShape store inst) (imports : InitializerImports store inst)
    (bindings : InitializerBindings store inst)
    (elementsValid : ∀ segment ∈ inst.module.module.env.elements.val,
      Itasca.ModuleSegments.elementValid inst.module.module.env segment)
    (dataValid : ∀ segment ∈ inst.module.module.tail.data.val,
      Itasca.ModuleData.Valid inst.module.module.env segment) :
    SegmentCodeReady store inst code code.slot_count.val := by
  obtain ⟨elements, datas, certificate⟩ := program
  refine ⟨pcBound, by rw [certificate.instructions]; simp, ?_⟩
  intro instruction member
  rw [certificate.instructions] at member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with (member | member) | rfl
  · obtain ⟨block, inBlocks, inBlock⟩ := List.mem_flatten.mp member
    obtain ⟨index, indexBound, indexed⟩ := List.mem_iff_getElem.mp inBlocks
    have sourceBound : index < inst.module.module.env.elements.val.length := by
      have := certificate.elementCount
      simp only [alloc.vec.Vec.length] at this
      omega
    let segment := inst.module.module.env.elements.val[index]
    have found : inst.module.module.env.elements.val[index]? = some segment := List.getElem?_eq_getElem sourceBound
    obtain ⟨instructions, read, emitted⟩ := certificate.elements index segment found
    have same : instructions = block := by
      rw [List.getElem?_eq_getElem indexBound, indexed] at read
      exact Option.some.inj read.symm
    subst instructions
    apply element_program_ready store inst code index segment block code.slot_count.val emitted sourceBound shape imports bindings
      (elementsValid segment (List.mem_of_getElem? found)) _ instruction inBlock
    intro length
    have cap := certificate.activeCapacity (Or.inl ⟨index, block, by rw [List.getElem?_eq_getElem indexBound, indexed], length⟩)
    simp [cap]
  · obtain ⟨block, inBlocks, inBlock⟩ := List.mem_flatten.mp member
    obtain ⟨index, indexBound, indexed⟩ := List.mem_iff_getElem.mp inBlocks
    have sourceBound : index < inst.module.module.tail.data.val.length := by
      have := certificate.dataCount
      simp only [alloc.vec.Vec.length] at this
      omega
    let segment := inst.module.module.tail.data.val[index]
    have found : inst.module.module.tail.data.val[index]? = some segment := List.getElem?_eq_getElem sourceBound
    obtain ⟨instructions, read, emitted⟩ := certificate.datas index segment found
    have same : instructions = block := by
      rw [List.getElem?_eq_getElem indexBound, indexed] at read
      exact Option.some.inj read.symm
    subst instructions
    apply data_program_ready store inst code index segment block code.slot_count.val emitted sourceBound shape imports bindings
      (dataValid segment (List.mem_of_getElem? found)) _ instruction inBlock
    intro length
    have cap := certificate.activeCapacity (Or.inr ⟨index, block, by rw [List.getElem?_eq_getElem indexBound, indexed], length⟩)
    simp [cap]
  · exact .done

/-- A nonreturning instruction cannot be the last instruction of a retained
initialization program. This supplies the decreasing finite-loop measure. -/
theorem SegmentCodeReady.next_bound {M : Type} {store : runtime.store.Store M}
    {inst code width position instruction} (ready : SegmentCodeReady store inst code width)
    (found : code.code.val[position]? = some instruction)
    (continues : segmentReturns instruction = false) : position + 1 < code.code.length := by
  have bound := (List.getElem?_eq_some_iff.mp found).1
  have last := ready.returnLast
  rw [List.getLast?_eq_getElem?] at last
  by_contra failure
  have same : position = code.code.val.length - 1 := by simp only [alloc.vec.Vec.length] at *; omega
  rw [← same, found] at last
  have instructionEq := Option.some.inj last
  simp [instructionEq, segmentReturns] at continues

end Itasca.Runtime.Store

end

/-! ## Segment Loop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
open Itasca.Runtime.Interp

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

end Itasca.Runtime.Store

end
