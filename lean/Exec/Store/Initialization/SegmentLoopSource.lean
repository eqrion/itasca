import Exec.Store.Initialization.SegmentLoopMetadata
import Exec.Store.Initialization.SegmentExtension
import Exec.Store.Initialization.SegmentStepSource
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

private theorem flow_return {pending : Nat} {instruction : runtime.bytecode.Instr} {rest : List runtime.bytecode.Instr}
    (flow : Code.SegmentFlow pending (instruction :: rest)) (returns : segmentReturns instruction = true) :
    rest = [] := by
  cases flow <;> simp_all [segmentReturns]

theorem segment_loop_source {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (sourceCode : CodeInterpretation)
    (store : runtime.store.Store M) (platform : P) (exec : runtime.interp.Execution)
    (instIndex function : Usize) (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (position : U32) (pending : Nat)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some code)
    (frames : exec.frames.val = [initializerFrame instIndex function position])
    (positionBound : position.val < code.code.length)
    (ready : SegmentCodeReady store inst code exec.slots.length)
    (flow : Code.SegmentFlow pending (code.code.val.drop position.val))
    (compatible : ∀ instruction ∈ code.code.val, SegmentBulkCompatible store inst code instruction)
    (globals : ∀ index address value, .GlobalGet 0#u32 index ∈ code.code.val →
      inst.globals.val[index.val]? = some address → store.globals.val[address.index.val]? = some value → value.ty.valtype = .I32)
    (shape : Shape view store) (sourceSyntax : StoreSyntax sourceCode store) (bounds : SegmentBounds store)
    (ambient : frame) (ambientWf : wf_frame ambient) (moduleEq : ambient.MODULE = decodeInstance store inst) :
    runtime.interp.run_synthetic_loop memory hooks floats allocator store platform exec (.Ok ()) ⦃ out =>
      StepsH (segmentState view sourceCode store ambient code exec.slots.val pending (code.code.val.drop position.val)) []
        ⟨⟨decodeStore view sourceCode out.1,ambient⟩,segmentResult out.2.2.2⟩ ⦄ := by
  let origin := segmentState view sourceCode store ambient code exec.slots.val pending (code.code.val.drop position.val)
  unfold runtime.interp.run_synthetic_loop
  apply loop.spec_decr_nat (fun state => segmentRemaining code state.2.2.1 state.2.2.2)
    (fun state => Shape view state.1 ∧ SegmentTypes store state.1 ∧ SegmentObjectMetadata view store state.1 ∧
      state.2.1 = platform ∧ state.2.2.1.slots.length = exec.slots.length ∧ SegmentStatus state.2.2.2 ∧
      ((state.2.2.1.frames.val = [] ∧ StepsH origin [] ⟨⟨decodeStore view sourceCode state.1,ambient⟩,segmentResult state.2.2.2⟩) ∨
        ∃ pc : U32, ∃ n : Nat, state.2.2.1.frames.val = [initializerFrame instIndex function pc] ∧
          pc.val < code.code.length ∧ Code.SegmentFlow n (code.code.val.drop pc.val) ∧
          StepsH origin [] ⟨⟨decodeStore view sourceCode state.1,ambient⟩,
            segmentAfter state.2.2.2 (vals (segmentPending state.2.2.1.slots.val n) ++ Code.segmentSource code (code.code.val.drop pc.val))⟩))
  · rintro ⟨current,host,machine,result⟩ ⟨currentShape,types,objects,hostEq,slots,status,cursor⟩
    dsimp only at currentShape types objects hostEq slots status cursor ⊢
    subst host
    cases result with
    | Err error =>
      simp only [runtime.interp.run_synthetic_loop.body,core.result.Result.is_ok,bind_ok,Bool.false_eq_true,↓reduceIte,ite_self,WP.spec_ok]
      rcases cursor with ⟨_,history⟩ | ⟨pc,n,_,_,_,history⟩
      · exact history
      · exact history
    | Ok unitValue =>
      cases unitValue
      rcases cursor with ⟨empty,history⟩ | ⟨pc,n,currentFrames,pcBound,currentFlow,history⟩
      · rw [synthetic_body_done memory hooks floats allocator machine current platform empty]
        simpa only [WP.spec_ok] using history
      · rw [synthetic_body_active memory hooks floats allocator machine current platform
          (by simp [alloc.vec.Vec.length,currentFrames])]
        have currentFound : current.instances.val[instIndex.val]? = some inst := by rw [objects.space.instances]; exact found
        have currentReady : SegmentCodeReady current inst code machine.slots.length := by
          rw [slots]; exact ready.transport objects.space
        let instruction := code.code.val[pc.val]
        let rest := code.code.val.drop (pc.val+1)
        have fetched : code.code.val[pc.val]? = some instruction := List.getElem?_eq_getElem pcBound
        have tail : code.code.val.drop pc.val = instruction :: rest := List.drop_eq_getElem_cons pcBound
        have currentCompatible := (compatible instruction (List.mem_of_getElem? fetched)).transport types
        have currentSyntax := sourceSyntax.instances_eq objects.space.instances
        have currentModuleEq : ambient.MODULE = decodeInstance current inst := by
          simpa only [decodeInstance,objects.space.signatures] using moduleEq
        have safe := segment_instruction_total memory hooks floats allocator view laws machine current platform instIndex function pc
          inst code instruction currentFound functionFound currentFrames fetched (lt_trans pcBound ready.size)
          (currentReady.instructions instruction (List.mem_of_getElem? fetched))
        have shaped := segment_instruction_shape memory hooks floats allocator view laws machine current platform instIndex function pc
          inst code instruction currentFound functionFound currentFrames fetched (lt_trans pcBound ready.size)
          (currentReady.instructions instruction (List.mem_of_getElem? fetched)) currentCompatible currentShape
        have metadata := segment_instruction_object_metadata memory hooks floats allocator view laws machine current platform instIndex function pc
          inst code instruction currentFound functionFound currentFrames fetched (lt_trans pcBound ready.size)
          (currentReady.instructions instruction (List.mem_of_getElem? fetched))
        have simulated := segment_instruction_source memory hooks floats allocator view laws sourceCode machine current platform instIndex function pc
          inst code instruction rest n (tail ▸ currentFlow) currentFound functionFound currentFrames fetched (lt_trans pcBound ready.size)
          (currentReady.instructions instruction (List.mem_of_getElem? fetched)) currentCompatible
          (by intro index address value instructionEq mapped issued
              apply globals index address value (instructionEq ▸ List.mem_of_getElem? fetched) mapped
              rw [objects.space.globals] at issued; exact issued)
          currentShape currentSyntax (objects.segment_bounds bounds) ambient ambientWf currentModuleEq
        step with segment_specs_and (segment_specs_and safe shaped) (segment_specs_and metadata simulated)
          as ⟨result,next,after,host,effect,newShape,newTypes,newObjects,nextPending,residual,reduction⟩
        change SegmentStepEffect machine current platform instIndex function pc instruction (result,next,after,host) at effect
        change (rest = [] ∧ nextPending = 0 ∨ Code.SegmentFlow nextPending rest) at residual
        have nextObjects := objects.trans newObjects
        have nextTypes := types.trans newTypes
        have nextSlots := effect.slots.trans slots
        have nextHost := effect.platform
        dsimp only at nextObjects nextTypes nextSlots nextHost
        subst host
        have combined : StepsH origin [] ⟨⟨decodeStore view sourceCode after,ambient⟩,
            segmentAfter result (vals (segmentPending next.slots.val nextPending) ++ Code.segmentSource code rest)⟩ := by
          have previous : StepsH origin [] (segmentState view sourceCode current ambient code machine.slots.val n (instruction::rest)) := by
            simpa only [segmentState,segmentAfter,tail] using history
          exact Spec.stepsH_trans previous reduction
        have nextFrames := effect.frames
        cases returns : segmentReturns instruction with
        | true =>
          have tailNil : rest = [] := flow_return (tail ▸ currentFlow) returns
          have pendingZero : nextPending = 0 := by
            rcases residual with ⟨_,same⟩ | flow
            · exact same
            · rw [tailNil] at flow; cases flow
          simp only [returns,↓reduceIte] at nextFrames
          refine ⟨newShape,nextTypes,nextObjects,rfl,nextSlots,effect.status,Or.inl ⟨nextFrames,?_⟩,?_⟩
          · cases result <;> simpa [pendingZero,tailNil,segmentPending,vals,Code.segmentSource,segmentAfter,segmentResult] using combined
          · cases result <;> simp [segmentRemaining,nextFrames,currentFrames,initializerFrame]
        | false =>
          simp only [returns,Bool.false_eq_true,↓reduceIte] at nextFrames
          obtain ⟨nextPc,nextValue,nextFrames⟩ := nextFrames
          have nextBound : nextPc.val < code.code.length := by have := ready.next_bound fetched returns; omega
          have nextFlow : Code.SegmentFlow nextPending rest := by
            rcases residual with ⟨empty,_⟩ | flow
            · have tooFar := List.drop_eq_nil_iff.mp empty
              change code.code.val.length ≤ pc.val+1 at tooFar
              change nextPc.val < code.code.val.length at nextBound
              omega
            · exact flow
          refine ⟨newShape,nextTypes,nextObjects,rfl,nextSlots,effect.status,
            Or.inr ⟨nextPc,nextPending,nextFrames,nextBound,?_,?_⟩,?_⟩
          · simpa only [nextValue] using nextFlow
          · simpa only [nextValue] using combined
          · cases result <;> simp only [segmentRemaining,nextFrames,currentFrames,initializerFrame]
            all_goals omega
  · refine ⟨shape,.refl _,.refl _ _,rfl,rfl,Or.inl rfl,Or.inr ⟨position,pending,frames,positionBound,flow,?_⟩⟩
    exact StepsH.refl (segmentState_wf view sourceCode store ambient code exec.slots.val pending _ shape sourceSyntax ambientWf)

end Itasca.Runtime.Store
