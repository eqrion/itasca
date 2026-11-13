import Itasca.Runtime.Store.Initialization.BulkMemory
import Itasca.Runtime.Spec.FloatPromote
import Itasca.Runtime.Spec.ModuleMembership
import Itasca.Runtime.Interp.Memory.MemoryCoreStep
import Itasca.Runtime.Spec.MemoryGrowth
import Itasca.Runtime.Store.Api.GrowthLimits

/-!
Sections, each formerly its own module: MemoryCopyLoops, MemoryCopy, MemoryFill.
-/

/-! ## MemoryCopyLoops -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Forward overlap copying retains unread source bytes, so its result uses
the source bytes as they were before the loop. -/
theorem memory_copy_forward (before : Slice U8) (destination source : Usize) (count : U64)
    (direction : destination.val ≤ source.val)
    (sourceBound : source.val+count.val ≤ before.length)
    (targetBound : destination.val+count.val ≤ before.length) :
    runtime.interp.bulk.execute_loop0 count destination source before 0#usize ⦃ after =>
      after.val = before.val.setSlice! destination.val (before.val.slice source.val (source.val+count.val)) ⦄ := by
  have countBound : count.val ≤ Usize.max := by have := before.property; scalar_tac
  have castCount := Interp.cast_usize_exact count countBound
  unfold runtime.interp.bulk.execute_loop0
  apply loop.spec_decr_nat (fun state => count.val-state.2.val)
    (fun state => state.2.val ≤ count.val ∧ Spec.Segment.CopyPrefix before.val state.1.val destination.val source.val state.2.val)
  · rintro ⟨current,index⟩ ⟨upper,copyState⟩
    dsimp only at upper copyState ⊢
    unfold runtime.interp.bulk.execute_loop0.body
    simp only [lift,bind_ok]
    split
    · rename_i more
      have less : index.val<count.val := by simpa only [UScalar.lt_equiv,castCount] using more
      have sourceInside : source.val+index.val < current.length := by
        change _ < current.val.length
        rw [copyState.length]
        change _ < before.length
        omega
      have targetInside : destination.val+index.val < current.length := by
        change _ < current.val.length
        rw [copyState.length]
        change _ < before.length
        omega
      step as ⟨src,srcEq⟩
      step as ⟨value,valueEq⟩
      step as ⟨dst,dstEq⟩
      step as ⟨updated,updatedEq⟩
      step as ⟨next,nextEq⟩
      refine ⟨by omega,?_,by omega⟩
      have updatedValues : updated.val = current.val.set (destination.val+index.val) current.val[source.val+index.val]! := by
        rw [updatedEq]
        simp only [Slice.set_val_eq,srcEq,dstEq,valueEq]
        congr 1
        exact (getElem!_pos current.val (source.val+index.val) sourceInside).symm
      have relation := copyState.write direction (by change _ < before.length; omega) (by change _ < before.length; omega)
      simpa only [updatedValues,nextEq] using relation
    · rename_i finished
      have last : index.val=count.val := by
        have notMore : ¬ index.val<count.val := by simpa only [UScalar.lt_equiv,castCount] using finished
        omega
      simp only [WP.spec_ok]
      exact (last ▸ copyState).complete sourceBound targetBound
  · exact ⟨by simp,by simpa using Spec.Segment.CopyPrefix.initial before.val destination.val source.val⟩

/-- Backward overlap copying preserves the unread source prefix. -/
theorem memory_copy_backward (before : Slice U8) (destination source count : Usize)
    (direction : source.val ≤ destination.val)
    (sourceBound : source.val+count.val ≤ before.length)
    (targetBound : destination.val+count.val ≤ before.length) :
    runtime.interp.bulk.execute_loop1 destination source before count ⦃ after =>
      after.val = before.val.setSlice! destination.val (before.val.slice source.val (source.val+count.val)) ⦄ := by
  unfold runtime.interp.bulk.execute_loop1
  apply loop.spec_decr_nat (fun state => state.2.val)
    (fun state => state.2.val ≤ count.val ∧ Spec.Segment.CopySuffix before.val state.1.val destination.val source.val state.2.val count.val)
  · rintro ⟨current,index⟩ ⟨upper,copyState⟩
    dsimp only at upper copyState ⊢
    unfold runtime.interp.bulk.execute_loop1.body
    split
    · rename_i more
      have positive : 0 < index.val := by simpa [UScalar.lt_equiv] using more
      have sourceInside : source.val+(index.val-1) < current.length := by
        change _ < current.val.length
        rw [copyState.length]
        change _ < before.length
        omega
      have targetInside : destination.val+(index.val-1) < current.length := by
        change _ < current.val.length
        rw [copyState.length]
        change _ < before.length
        omega
      step as ⟨next,nextEq⟩
      step as ⟨src,srcEq⟩
      step as ⟨value,valueEq⟩
      step as ⟨dst,dstEq⟩
      step as ⟨updated,updatedEq⟩
      refine ⟨by omega,?_,by omega⟩
      have updatedValues : updated.val = current.val.set (destination.val+(index.val-1)) current.val[source.val+(index.val-1)]! := by
        rw [updatedEq]
        simp only [Slice.set_val_eq,srcEq,dstEq,valueEq,nextEq]
        congr 1
        exact (getElem!_pos current.val (source.val+(index.val-1)) sourceInside).symm
      have relation := copyState.write direction positive upper (by change _ ≤ before.length; omega) (by change _ ≤ before.length; omega)
      simpa only [updatedValues,nextEq] using relation
    · rename_i finished
      have last : index.val=0 := by
        have notMore : ¬ 0 < index.val := by simpa [UScalar.lt_equiv] using finished
        omega
      simp only [WP.spec_ok]
      exact (last ▸ copyState).complete sourceBound targetBound
  · exact ⟨Nat.le_refl _,Spec.Segment.CopySuffix.initial before.val destination.val source.val count.val⟩
end Itasca.Runtime.Store

end

/-! ## MemoryCopy -/

section

/-!
Memory copy effects, mutation and decoded snapshot semantics. These retain success and error distinctions used by preparation and instantiation.
-/

/-! ## Memory Copy Effect -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

def MemoryCopyEffect {M : Type} (view : M → Slice U8) (store : runtime.store.Store M)
    (address : Usize) (memory : runtime.store.MemInst M) (destination source count : U64)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M) : Prop :=
  if destination.val+count.val ≤ (view memory.buf).length ∧ source.val+count.val ≤ (view memory.buf).length then
    ∃ buffer, out = (.Ok (),{store with memories := store.memories.set address {memory with buf := buffer}}) ∧
      (view buffer).val = (view memory.buf).val.setSlice! destination.val ((view memory.buf).val.slice source.val (source.val+count.val))
  else out = (.Err (.Trap .MemoryOutOfBounds),store)

/-- Memory copy validates both ranges before any write and preserves the
original source bytes even when the ranges overlap. -/
theorem bulk_memory_copy {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws ops view)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (operand : U32) (inst : runtime.store.ModuleInst) (address : runtime.MemoryAddr)
    (memory : runtime.store.MemInst M) (destination source count : U64)
    (found : store.instances.val[instIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some address)
    (target : store.memories.val[address.index.val]? = some memory)
    (destinationSlot : slots.val[base.val+operand.val]? = some destination)
    (sourceSlot : slots.val[base.val+operand.val+1]? = some source)
    (countSlot : slots.val[base.val+operand.val+2]? = some count) :
    runtime.interp.bulk.execute ops store instIndex function base slots (.MemoryCopy operand) ⦃ out =>
      MemoryCopyEffect view store address.index memory (bulkWord destination) (bulkWord source) (bulkWord count) out ⦄ := by
  have bound := (List.getElem?_eq_some_iff.mp countSlot).1
  simp only [runtime.interp.bulk.execute,lift,bind_ok]
  step as ⟨position,positionEq⟩
  have pos : position.val = base.val+operand.val := by simpa only [U32.cast_Usize_val_eq] using positionEq
  rw [Compiler.initializer_slice_index slots position destination (by simpa only [pos] using destinationSlot)]
  simp only [bind_ok,lift]
  step as ⟨position1,position1Eq⟩
  step as ⟨position2,position2Eq⟩
  have pos2 : position2.val = base.val+operand.val+1 := by simpa only [position1Eq,U32.cast_Usize_val_eq] using position2Eq
  rw [Compiler.initializer_slice_index slots position2 source (by simpa only [pos2] using sourceSlot)]
  simp only [bind_ok,lift]
  step as ⟨position3,position3Eq⟩
  step as ⟨position4,position4Eq⟩
  have pos4 : position4.val = base.val+operand.val+2 := by simpa only [position3Eq,U32.cast_Usize_val_eq] using position4Eq
  rw [Compiler.initializer_slice_index slots position4 count (by simpa only [pos4] using countSlot)]
  simp only [bind_ok,lift]
  step with Interp.vec_index_given store.instances instIndex inst found as ⟨actual,actualEq⟩
  subst actual
  step with Interp.vec_index_given inst.memories 0#usize address mapped as ⟨actual,actualEq⟩
  subst actual
  step with Interp.vec_index_given store.memories address.index memory target as ⟨actual,actualEq⟩
  subst actual
  rw [laws.read,bind_ok]
  step with Interp.range_effect (bulkWord destination) (bulkWord count) (Slice.len (view memory.buf))
    .MemoryOutOfBounds as ⟨result,rangeEffect⟩
  by_cases fits : (bulkWord destination).val+(bulkWord count).val ≤ (view memory.buf).length
  · change (if (bulkWord destination).val+(bulkWord count).val ≤ (view memory.buf).length then _ else _) at rangeEffect
    rw [if_pos fits] at rangeEffect
    obtain ⟨dst,rfl,dstStart,dstEnd⟩ := rangeEffect
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step with Interp.range_effect (bulkWord source) (bulkWord count) (Slice.len (view memory.buf))
      .MemoryOutOfBounds as ⟨result,sourceEffect⟩
    by_cases sourceFits : (bulkWord source).val+(bulkWord count).val ≤ (view memory.buf).length
    · change (if (bulkWord source).val+(bulkWord count).val ≤ (view memory.buf).length then _ else _) at sourceEffect
      rw [if_pos sourceFits] at sourceEffect
      obtain ⟨src,rfl,srcStart,srcEnd⟩ := sourceEffect
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      have memoryBound := (List.getElem?_eq_some_iff.mp target).1
      have memoryRead := (List.getElem?_eq_some_iff.mp target).2
      step as ⟨actualMemory,memoryBack,actualMemoryEq,memoryBackEq⟩
      have sameMemory : actualMemory = memory := actualMemoryEq.trans memoryRead
      rw [sameMemory]
      obtain ⟨back,write,viewBack⟩ := laws.write memory.buf
      rw [write,bind_ok]
      have dstOrder : dst.start ≤ dst.end := by scalar_tac
      have dstBound : dst.end.val ≤ (view memory.buf).length := by omega
      have srcOrder : src.start ≤ src.end := by scalar_tac
      have srcBound : src.end.val ≤ (view memory.buf).length := by omega
      have countBound : (bulkWord count).val ≤ Usize.max := by have := (view memory.buf).property; scalar_tac
      have castCount := Interp.cast_usize_exact (bulkWord count) countBound
      have rawSrcBound : src.end.val ≤ (view memory.buf).val.length := srcBound
      have rawDstBound : dst.end.val ≤ (view memory.buf).val.length := dstBound
      have castExpanded : (UScalar.cast .Usize (UScalar.cast .U64 (UScalar.cast .U32 count))).val = (bulkWord count).val := castCount
      split
      · rename_i leftCase
        have disjoint : dst.end.val ≤ src.start.val := by simpa only [UScalar.le_equiv] using leftCase
        step as ⟨left,right,splitBack,leftLength,rightLength,leftValues,rightValues,splitBackEq⟩
        step as ⟨targetSlice,targetBack,targetValues,targetLength,targetBackEq⟩
        step as ⟨sourceSlice,sourceValues,sourceLength⟩
        have sameLength : targetSlice.length = sourceSlice.length := by omega
        step as ⟨copied,copiedEq⟩
        subst copied
        have leftFilledLength : (targetBack sourceSlice).length = src.start.val := by rw [targetBackEq]; simpa using leftLength
        have output := splitBackEq (targetBack sourceSlice) right leftFilledLength rightLength
        simp only [MemoryCopyEffect,fits,sourceFits,and_self,↓reduceIte]
        refine ⟨back (splitBack (targetBack sourceSlice,right)),by simp only [memoryBackEq],?_⟩
        rw [viewBack _ output.2,output.1,targetBackEq,Slice.setSlice!_val,leftValues,rightValues,sourceValues]
        simp only [List.slice_zero_j,castExpanded]
        rw [rightValues]
        have payloadLength : ((view memory.buf).val.drop src.start.val |>.take (bulkWord count).val).length = (bulkWord count).val := by simp only [List.length_take,List.length_drop]; omega
        rw [Spec.Segment.set_slice_split_left _ _ _ _ (by omega) (by omega)]
        simp only [List.slice,srcStart,srcEnd,dstStart,Nat.add_sub_cancel_left,castExpanded]
      · split
        · rename_i rightCase
          have disjoint : src.end.val ≤ dst.start.val := by simpa only [UScalar.le_equiv] using rightCase
          step as ⟨left,right,splitBack,leftLength,rightLength,leftValues,rightValues,splitBackEq⟩
          step as ⟨targetSlice,targetBack,targetValues,targetLength,targetBackEq⟩
          step as ⟨sourceSlice,sourceValues,sourceLength⟩
          have sameLength : targetSlice.length = sourceSlice.length := by omega
          step as ⟨copied,copiedEq⟩
          subst copied
          have rightFilledLength : (targetBack sourceSlice).length = (view memory.buf).length-dst.start.val := by
            change (targetBack sourceSlice).val.length = _
            rw [targetBackEq,List.length_setSlice!]
            exact rightLength
          have output := splitBackEq left (targetBack sourceSlice) leftLength rightFilledLength
          simp only [MemoryCopyEffect,fits,sourceFits,and_self,↓reduceIte]
          refine ⟨back (splitBack (left,targetBack sourceSlice)),by simp only [memoryBackEq],?_⟩
          rw [viewBack _ output.2,output.1,targetBackEq,leftValues,rightValues,sourceValues,leftValues]
          have sliceSame : ((view memory.buf).val.take dst.start.val).slice src.start.val src.end.val =
              (view memory.buf).val.slice src.start.val src.end.val := by
            simp only [List.slice,List.drop_take,List.take_take]
            congr 1
            omega
          rw [sliceSame]
          have payloadLength : ((view memory.buf).val.slice src.start.val src.end.val).length = (bulkWord count).val := by rw [List.slice_length]; omega
          rw [Spec.Segment.set_slice_split_right _ _ _ (by omega)]
          simp only [srcStart,srcEnd,dstStart]
        · split
          · rename_i forward
            have direction : dst.start.val ≤ src.start.val := by simpa only [UScalar.le_equiv] using forward
            step with memory_copy_forward (view memory.buf) dst.start src.start (bulkWord count)
              direction (by omega) (by omega) as ⟨copied,copiedValues⟩
            have copiedLength : copied.length = (view memory.buf).length := by simpa only [Slice.length,List.length_setSlice!] using congrArg List.length copiedValues
            simp only [MemoryCopyEffect,fits,sourceFits,and_self,↓reduceIte]
            refine ⟨back copied,by simp only [memoryBackEq],?_⟩
            rw [viewBack _ copiedLength,copiedValues]
            simp only [srcStart,dstStart]
          · rename_i backward
            have direction : src.start.val ≤ dst.start.val := by
              have notForward : ¬ dst.start.val ≤ src.start.val := by simpa only [UScalar.le_equiv] using backward
              omega
            step with memory_copy_backward (view memory.buf) dst.start src.start (UScalar.cast .Usize (bulkWord count))
              direction (by omega) (by omega) as ⟨copied,copiedValues⟩
            have copiedLength : copied.length = (view memory.buf).length := by simpa only [Slice.length,List.length_setSlice!] using congrArg List.length copiedValues
            simp only [MemoryCopyEffect,fits,sourceFits,and_self,↓reduceIte]
            refine ⟨back copied,by simp only [memoryBackEq],?_⟩
            rw [viewBack _ copiedLength,copiedValues]
            simp only [srcStart,dstStart,castCount]
    · change (if (bulkWord source).val+(bulkWord count).val ≤ (view memory.buf).length then _ else _) at sourceEffect
      rw [if_neg sourceFits] at sourceEffect
      rw [sourceEffect]
      simp_all [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,MemoryCopyEffect]
  · change (if (bulkWord destination).val+(bulkWord count).val ≤ (view memory.buf).length then _ else _) at rangeEffect
    rw [if_neg fits] at rangeEffect
    rw [rangeEffect]
    simp_all [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,MemoryCopyEffect]
end Itasca.Runtime.Store

end

/-! ## Memory Copy Mutation -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca.Runtime.Interp

theorem MemoryCopyEffect.mutation {M : Type} (view : M → Slice U8) (store : runtime.store.Store M)
    (address : runtime.MemoryAddr) (memory : runtime.store.MemInst M) (destination source count : U64)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M)
    (effect : MemoryCopyEffect view store address.index memory destination source count out) :
    FrameStoreMetadata store out.2 ∧
    ((out.1 = .Ok () ∧ MemoryMutation view store out.2 address memory) ∨
      (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧ out.2 = store)) := by
  unfold MemoryCopyEffect at effect
  split at effect
  · obtain ⟨buffer,rfl,filled⟩ := effect
    refine ⟨⟨rfl,rfl,rfl,rfl⟩,Or.inl ⟨rfl,buffer,rfl,?_⟩⟩
    simpa only [Slice.length,List.length_setSlice!] using congrArg List.length filled
  · rw [effect]
    exact ⟨⟨rfl,rfl,rfl,rfl⟩,Or.inr ⟨rfl,rfl⟩⟩
end Itasca.Runtime.Store

end

/-! ## Memory Copy Semantics -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt

theorem memory_copy_decodes {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (address : runtime.MemoryAddr) (memory : runtime.store.MemInst M)
    (destination source count : Nat) (buffer : M)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.memories.val[0]? = some address)
    (target : store.memories.val[address.index.val]? = some memory)
    (inside : source+count ≤ (view memory.buf).length ∧ destination+count ≤ (view memory.buf).length)
    (copied : (view buffer).val = (view memory.buf).val.setSlice! destination ((view memory.buf).val.slice source (source+count))) :
    decodeStore view code {store with memories := store.memories.set address.index {memory with buf := buffer}} =
      Spec.Segment.memoryCopy (decodeStore view code store) ambient destination source count := by
  have memoryRead : ambient.MODULE.MEMS[0]! = address.index.val := by
    simp [moduleEq,decodeInstance,List.getElem!_eq_getElem?_getD,mapped]
  have memoryLookup : (decodeStore view code store).MEMS[address.index.val]! = decodeMemory view memory := by
    simp [decodeStore,List.getElem!_eq_getElem?_getD,target]
  have lengthEq : (view buffer).length = (view memory.buf).length := by
    simpa only [Slice.length,List.length_setSlice!] using congrArg List.length copied
  have bytesEq : decodeBytes (view buffer).val =
      (decodeBytes (view memory.buf).val).setSlice! destination ((decodeBytes (view memory.buf).val).slice source (source+count)) := by
    rw [←Spec.Segment.copy_into_eq_set_slice _ _ _ _ _ (by simpa [decodeBytes] using inside.1) (by simpa [decodeBytes] using inside.2)]
    unfold decodeBytes
    rw [copied,←Spec.Segment.copy_into_eq_set_slice _ _ _ _ _ inside.1 inside.2]
    exact copy_into_map _ _ _ _ _ _ inside.1
  unfold Spec.Segment.memoryCopy
  rw [memoryRead,memoryLookup]
  unfold decodeStore
  simp only [alloc.vec.Vec.set_val_eq,List.map_set]
  simp only [decodeMemory,lengthEq,bytesEq,Spec.Segment.withBytes]
  rfl

end Itasca.Runtime.Store

end

end

/-! ## MemoryFill -/

section

/-!
Memory fill from the extracted handler to its decoded source effect.

`MemoryFillEffect` records the checked byte interval and unchanged-state trap.
The handler, mutation, and decoding lemmas supply the memory-fill execution
construction and the common store-mutation facts.
-/

/-! ## Handler effect -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

def MemoryFillEffect {M : Type} (view : M → Slice U8) (store : runtime.store.Store M)
    (address : Usize) (memory : runtime.store.MemInst M) (destination count : U64) (value : U8)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M) : Prop :=
  if destination.val+count.val ≤ (view memory.buf).length then
    ∃ buffer, out = (.Ok (),{store with memories := store.memories.set address {memory with buf := buffer}}) ∧
      (view buffer).val = (view memory.buf).val.setSlice! destination.val (List.replicate count.val value)
  else out = (.Err (.Trap .MemoryOutOfBounds),store)

/-- The actual memory.fill handler writes the low byte only, after validating
its complete destination range. -/
theorem bulk_memory_fill {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws ops view)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (operand : U32) (inst : runtime.store.ModuleInst) (address : runtime.MemoryAddr)
    (memory : runtime.store.MemInst M) (destination value count : U64)
    (found : store.instances.val[instIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some address)
    (target : store.memories.val[address.index.val]? = some memory)
    (destinationSlot : slots.val[base.val+operand.val]? = some destination)
    (valueSlot : slots.val[base.val+operand.val+1]? = some value)
    (countSlot : slots.val[base.val+operand.val+2]? = some count) :
    runtime.interp.bulk.execute ops store instIndex function base slots (.MemoryFill operand) ⦃ out =>
      MemoryFillEffect view store address.index memory (bulkWord destination) (bulkWord count)
        (UScalar.cast .U8 (UScalar.cast .U32 value)) out ⦄ := by
  have bound := (List.getElem?_eq_some_iff.mp countSlot).1
  simp only [runtime.interp.bulk.execute,lift,bind_ok]
  step as ⟨position,positionEq⟩
  have pos : position.val = base.val+operand.val := by simpa only [U32.cast_Usize_val_eq] using positionEq
  rw [Compiler.initializer_slice_index slots position destination (by simpa only [pos] using destinationSlot)]
  simp only [bind_ok,lift]
  step as ⟨position1,position1Eq⟩
  step as ⟨position2,position2Eq⟩
  have pos2 : position2.val = base.val+operand.val+1 := by simpa only [position1Eq,U32.cast_Usize_val_eq] using position2Eq
  rw [Compiler.initializer_slice_index slots position2 value (by simpa only [pos2] using valueSlot)]
  simp only [bind_ok,lift]
  step as ⟨position3,position3Eq⟩
  step as ⟨position4,position4Eq⟩
  have pos4 : position4.val = base.val+operand.val+2 := by simpa only [position3Eq,U32.cast_Usize_val_eq] using position4Eq
  rw [Compiler.initializer_slice_index slots position4 count (by simpa only [pos4] using countSlot)]
  simp only [bind_ok,lift]
  step with Interp.vec_index_given store.instances instIndex inst found as ⟨actual,actualEq⟩
  subst actual
  step with Interp.vec_index_given inst.memories 0#usize address mapped as ⟨actual,actualEq⟩
  subst actual
  step with Interp.vec_index_given store.memories address.index memory target as ⟨actual,actualEq⟩
  subst actual
  rw [laws.read,bind_ok]
  step with Interp.range_effect (bulkWord destination) (bulkWord count) (Slice.len (view memory.buf))
    .MemoryOutOfBounds as ⟨result,rangeEffect⟩
  by_cases fits : (bulkWord destination).val+(bulkWord count).val ≤ (view memory.buf).length
  · change (if (bulkWord destination).val+(bulkWord count).val ≤ (view memory.buf).length then _ else _) at rangeEffect
    rw [if_pos fits] at rangeEffect
    obtain ⟨dst,rfl,dstStart,dstEnd⟩ := rangeEffect
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have memoryBound := (List.getElem?_eq_some_iff.mp target).1
    have memoryRead := (List.getElem?_eq_some_iff.mp target).2
    step as ⟨actualMemory,memoryBack,actualMemoryEq,memoryBackEq⟩
    have sameMemory : actualMemory = memory := actualMemoryEq.trans memoryRead
    rw [sameMemory]
    obtain ⟨back,write,viewBack⟩ := laws.write memory.buf
    rw [write,bind_ok]
    have dstOrder : dst.start ≤ dst.end := by scalar_tac
    have dstBound : dst.end.val ≤ (view memory.buf).length := by omega
    step as ⟨targetSlice,targetBack,targetValues,targetLength,targetBackEq⟩
    step with core.slice.Slice.fill.spec core.clone.CloneU8 targetSlice
      (UScalar.cast .U8 (UScalar.cast .U32 value)) (by simp [core.clone.CloneU8]) as ⟨filled,filledLength,filledValues⟩
    simp only [MemoryFillEffect,fits,↓reduceIte]
    refine ⟨back (targetBack filled),?_,?_⟩
    · simp only [memoryBackEq]
    · rw [targetBackEq,viewBack _ (by simp)]
      rw [Slice.setSlice!_val,filledValues,dstStart,targetLength,dstStart,dstEnd,Nat.add_sub_cancel_left]
  · change (if (bulkWord destination).val+(bulkWord count).val ≤ (view memory.buf).length then _ else _) at rangeEffect
    rw [if_neg fits] at rangeEffect
    rw [rangeEffect]
    simp_all [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,MemoryFillEffect]
end Itasca.Runtime.Store

end

/-! ## Metadata and mutation -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca.Runtime.Interp

theorem MemoryFillEffect.mutation {M : Type} (view : M → Slice U8) (store : runtime.store.Store M)
    (address : runtime.MemoryAddr) (memory : runtime.store.MemInst M) (destination count : U64) (value : U8)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M)
    (effect : MemoryFillEffect view store address.index memory destination count value out) :
    FrameStoreMetadata store out.2 ∧
    ((out.1 = .Ok () ∧ MemoryMutation view store out.2 address memory) ∨
      (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧ out.2 = store)) := by
  unfold MemoryFillEffect at effect
  split at effect
  · obtain ⟨buffer,rfl,filled⟩ := effect
    refine ⟨⟨rfl,rfl,rfl,rfl⟩,Or.inl ⟨rfl,buffer,rfl,?_⟩⟩
    simpa only [Slice.length,List.length_setSlice!] using congrArg List.length filled
  · rw [effect]
    exact ⟨⟨rfl,rfl,rfl,rfl⟩,Or.inr ⟨rfl,rfl⟩⟩
end Itasca.Runtime.Store

end

/-! ## Decoded source effect -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt

private theorem fill_map_set_modify {T U : Type} (decode : T → U) (change : U → U)
    (values : List T) (index : Nat) (old replacement : T)
    (found : values[index]? = some old) (same : decode replacement = change (decode old)) :
    (values.set index replacement).map decode = (values.map decode).modify index change := by
  induction values generalizing index with
  | nil => simp at found
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at found
      subst old
      simpa using same
    | succ index =>
      simp only [List.getElem?_cons_succ] at found
      simpa using ih index found

theorem memory_fill_decodes {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (address : runtime.MemoryAddr) (memory : runtime.store.MemInst M)
    (destination count : Nat) (value : U32) (buffer : M)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.memories.val[0]? = some address)
    (target : store.memories.val[address.index.val]? = some memory)
    (memoryBound : (view memory.buf).length ≤ 2^32)
    (inside : destination+count ≤ (view memory.buf).length)
    (filled : (view buffer).val = (view memory.buf).val.setSlice! destination
      (List.replicate count (UScalar.cast .U8 value))) :
    decodeStore view code {store with memories := store.memories.set address.index {memory with buf := buffer}} =
      Spec.Segment.memoryFill (decodeStore view code store) ambient destination value.val count := by
  have memoryRead : ambient.MODULE.MEMS[0]! = address.index.val := by
    simp [moduleEq,decodeInstance,List.getElem!_eq_getElem?_getD,mapped]
  have memoryLookup : fun_mem ⟨decodeStore view code store,ambient⟩ (.mk_uN 0) = decodeMemory view memory := by
    simp [fun_mem,moduleEq,decodeInstance,decodeStore,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,target]
  have lengthEq : (view buffer).length = (view memory.buf).length := by
    simpa only [Slice.length,List.length_setSlice!] using congrArg List.length filled
  have byteEq : byte.mk_byte (UScalar.cast .U8 value).val = Spec.Segment.fillByte value.val := by
    simp [Spec.Segment.fillByte]
  have bytesEq : decodeBytes (view buffer).val =
      Spec.Segment.fillInto (decodeBytes (view memory.buf).val) destination (Spec.Segment.fillByte value.val) count := by
    unfold decodeBytes
    rw [filled,←Spec.Segment.fill_into_eq_set_slice _ _ _ _ inside,Spec.Segment.fill_into_map,byteEq]
  have lists := fill_map_set_modify (decodeMemory view)
    (fun m => {m with BYTES := Spec.Segment.fillInto m.BYTES destination (Spec.Segment.fillByte value.val) count})
    store.memories.val address.index.val memory {memory with buf := buffer} target
    (by simp only [decodeMemory,lengthEq,bytesEq])
  have addressBound : ambient.MODULE.MEMS[0]! < (decodeStore view code store).MEMS.length := by
    rw [memoryRead]
    simpa [decodeStore] using (List.getElem?_eq_some_iff.mp target).1
  rw [Spec.Segment.memory_fill_eq _ _ _ _ _ addressBound
    (by simpa [memoryLookup,decodeMemory,decodeBytes] using memoryBound)
    (by simpa [memoryLookup,decodeMemory,decodeBytes] using inside),memoryRead]
  unfold decodeStore
  simp only [alloc.vec.Vec.set_val_eq,lists]
  rfl

end Itasca.Runtime.Store

end

end
