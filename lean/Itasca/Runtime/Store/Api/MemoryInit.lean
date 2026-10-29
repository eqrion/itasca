import Itasca.Runtime.Representation.Collection
import Itasca.Runtime.Spec.MemoryInit
import Itasca.Runtime.Spec.SegmentCopySlice
import Itasca.Runtime.Store.Api.TableInit

/-!
Memory initialization execution and decoded source effect. These retain success and error distinctions used by preparation and instantiation.
-/

/-! ## Memory Init Semantics -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt

theorem memory_init_decodes {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (dataIndex : U32) (memoryAddress : runtime.MemoryAddr) (dataAddress : Usize)
    (memory : runtime.store.MemInst M) (segment : runtime.store.DataInst)
    (destination source count : Nat) (buffer : M)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (memoryMapped : inst.memories.val[0]? = some memoryAddress)
    (dataMapped : inst.datas.val[dataIndex.val]? = some dataAddress)
    (target : store.memories.val[memoryAddress.index.val]? = some memory)
    (resolved : store.datas.val[dataAddress.val]? = some segment)
    (memoryBound : (view memory.buf).length ≤ 2^32)
    (dataBound : segment.bytes.length ≤ 2^32)
    (inside : source+count ≤ segment.bytes.length ∧ destination+count ≤ (view memory.buf).length)
    (copied : (view buffer).val = (view memory.buf).val.setSlice! destination (segment.bytes.val.slice source (source+count))) :
    decodeStore view code {store with memories := store.memories.set memoryAddress.index {memory with buf := buffer}} =
      Spec.Segment.memoryInit (decodeStore view code store) ambient dataIndex.val destination source count := by
  have memoryRead : ambient.MODULE.MEMS[0]! = memoryAddress.index.val := by
    simp [moduleEq,decodeInstance,List.getElem!_eq_getElem?_getD,memoryMapped]
  have memoryLookup : fun_mem ⟨decodeStore view code store,ambient⟩ (.mk_uN 0) = decodeMemory view memory := by
    simp [fun_mem,moduleEq,decodeInstance,decodeStore,proj_uN_0,List.getElem!_eq_getElem?_getD,memoryMapped,target]
  have dataRead : fun_data ⟨decodeStore view code store,ambient⟩ (.mk_uN dataIndex.val) = decodeData segment := by
    simp [fun_data,moduleEq,decodeInstance,decodeStore,proj_uN_0,List.getElem!_eq_getElem?_getD,dataMapped,resolved]
  have lengthEq : (view buffer).length = (view memory.buf).length := by
    simpa only [Slice.length,List.length_setSlice!] using congrArg List.length copied
  have bytesEq : decodeBytes (view buffer).val =
      Spec.Segment.copyInto (decodeBytes (view memory.buf).val) (decodeBytes segment.bytes.val) destination source count := by
    unfold decodeBytes
    rw [copied,←Spec.Segment.copyInto_eq_setSlice _ _ _ _ _ inside.1 inside.2]
    exact copyInto_map _ _ _ _ _ _ inside.1
  have lists := Itasca.Runtime.Representation.map_set_modify (decodeMemory view)
    (fun m => {m with BYTES := Spec.Segment.copyInto m.BYTES (decodeData segment).BYTES destination source count})
    store.memories.val memoryAddress.index.val memory {memory with buf := buffer} target
    (by simp only [decodeMemory,decodeData,lengthEq,bytesEq])
  have addressBound : ambient.MODULE.MEMS[0]! < (decodeStore view code store).MEMS.length := by
    rw [memoryRead]
    simpa [decodeStore] using (List.getElem?_eq_some_iff.mp target).1
  rw [Spec.Segment.memoryInit_eq _ _ _ _ _ _ addressBound
    (by simpa [memoryLookup,decodeMemory,decodeBytes] using memoryBound)
    (by simpa [dataRead,decodeData,decodeBytes] using dataBound)
    (by simpa [memoryLookup,dataRead,decodeMemory,decodeData,decodeBytes] using inside),memoryRead,dataRead]
  unfold decodeStore
  simp only [alloc.vec.Vec.set_val_eq,lists]
  rfl

theorem MemoryInitializationEffect.refines {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (dataIndex : U32) (memoryAddress : runtime.MemoryAddr) (dataAddress : Usize)
    (memory : runtime.store.MemInst M) (segment : runtime.store.DataInst)
    (destination source count : U64) (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M)
    (effect : MemoryInitializationEffect view store memoryAddress.index memory segment destination source count out)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (memoryMapped : inst.memories.val[0]? = some memoryAddress)
    (dataMapped : inst.datas.val[dataIndex.val]? = some dataAddress)
    (target : store.memories.val[memoryAddress.index.val]? = some memory)
    (resolved : store.datas.val[dataAddress.val]? = some segment)
    (shape : Shape view store) (sourceSyntax : StoreSyntax code store) (ambientWf : wf_frame ambient)
    (dataBound : segment.bytes.length < 2^32)
    (dstBound : destination.val < 2^32) (srcBound : source.val < 2^32) (countBound : count.val < 2^32) :
    StepsH ⟨⟨decodeStore view code store,ambient⟩,Spec.Segment.operands destination.val source.val count.val ++
      [.MEMORY_INIT (.mk_uN dataIndex.val)]⟩ []
      ⟨⟨decodeStore view code out.2,ambient⟩,segmentResult out.1⟩ := by
  have memoryRead : fun_mem ⟨decodeStore view code store,ambient⟩ (.mk_uN 0) = decodeMemory view memory := by
    simp [fun_mem,moduleEq,decodeInstance,decodeStore,proj_uN_0,List.getElem!_eq_getElem?_getD,memoryMapped,target]
  have dataRead : fun_data ⟨decodeStore view code store,ambient⟩ (.mk_uN dataIndex.val) = decodeData segment := by
    simp [fun_data,moduleEq,decodeInstance,decodeStore,proj_uN_0,List.getElem!_eq_getElem?_getD,dataMapped,resolved]
  have wf := decodeStore_wf view code store shape sourceSyntax
  unfold MemoryInitializationEffect at effect
  split at effect
  · rename_i inside
    obtain ⟨buffer,rfl,copied⟩ := effect
    simp only [segmentResult]
    rw [memory_init_decodes view code store inst ambient dataIndex memoryAddress dataAddress memory segment
      destination.val source.val count.val buffer moduleEq memoryMapped dataMapped target resolved
      (shape.memories memory (List.mem_of_getElem? target)).length_bound (by omega) ⟨inside.2,inside.1⟩ copied]
    apply Spec.Segment.memory_init_steps _ _ _ _ _ _ wf ambientWf dstBound srcBound countBound (by scalar_tac)
    · simpa [moduleEq,decodeInstance] using (List.getElem?_eq_some_iff.mp memoryMapped).1
    · have addressRead : ambient.MODULE.MEMS[0]! = memoryAddress.index.val := by
        simp [moduleEq,decodeInstance,List.getElem!_eq_getElem?_getD,memoryMapped]
      rw [addressRead]
      simpa [decodeStore] using (List.getElem?_eq_some_iff.mp target).1
    · rw [dataRead]
      exact decodeBytes_wf segment.bytes.val
    · simpa [memoryRead,dataRead,decodeMemory,decodeData,decodeBytes] using And.intro inside.2 inside.1
  · rename_i outside
    rw [effect]
    apply Spec.stepsH_single
    apply Spec.Segment.memory_init_trap _ _ _ _ _ _ wf ambientWf dstBound srcBound countBound (by scalar_tac)
    simp only [memoryRead,dataRead,decodeMemory,decodeData,decodeBytes,List.length_map]
    simp only [alloc.vec.Vec.length,Slice.length] at outside
    omega

end Itasca.Runtime.Store

end

/-! ## Memory Init Execution -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt

theorem bulk_memory_init_refines {M : Type} (memoryOps : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memoryOps view) (sourceCode : CodeInterpretation)
    (store : runtime.store.Store M) (instIndex function : Usize) (slots : Slice U64)
    (inst : runtime.store.ModuleInst) (dataIndex : U32) (address : Usize) (memoryAddress : runtime.MemoryAddr)
    (memory : runtime.store.MemInst M) (segment : runtime.store.DataInst)
    (destination source count : U64) (ambient : frame)
    (found : store.instances.val[instIndex.val]? = some inst)
    (mapped : inst.datas.val[dataIndex.val]? = some address)
    (resolved : store.datas.val[address.val]? = some segment)
    (memoryMapped : inst.memories.val[0]? = some memoryAddress)
    (target : store.memories.val[memoryAddress.index.val]? = some memory)
    (destinationSlot : slots.val[0]? = some destination)
    (sourceSlot : slots.val[1]? = some source) (countSlot : slots.val[2]? = some count)
    (shape : Shape view store) (sourceSyntax : StoreSyntax sourceCode store) (ambientWf : wf_frame ambient)
    (moduleEq : ambient.MODULE = decodeInstance store inst) (dataBound : segment.bytes.length < 2^32) :
    runtime.interp.bulk.execute memoryOps store instIndex function 0#usize slots (.MemoryInit 0#u32 dataIndex)
      ⦃ out => StepsH ⟨⟨decodeStore view sourceCode store,ambient⟩,
        Spec.Segment.operands (bulkWord destination).val (bulkWord source).val (bulkWord count).val ++
          [.MEMORY_INIT (.mk_uN dataIndex.val)]⟩ []
        ⟨⟨decodeStore view sourceCode out.2,ambient⟩,segmentResult out.1⟩ ⦄ := by
  apply WP.spec_mono (bulk_memory_init memoryOps view laws store instIndex function slots inst dataIndex address
    memoryAddress memory segment destination source count found mapped resolved memoryMapped target
    destinationSlot sourceSlot countSlot)
  intro out effect
  exact effect.refines view sourceCode store inst ambient dataIndex memoryAddress address memory segment
    (bulkWord destination) (bulkWord source) (bulkWord count) out moduleEq memoryMapped mapped target resolved
    shape sourceSyntax ambientWf dataBound (by scalar_tac) (by scalar_tac) (by scalar_tac)

end Itasca.Runtime.Store

end
