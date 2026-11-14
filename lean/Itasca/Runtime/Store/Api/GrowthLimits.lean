import Itasca.Runtime.Store.Invariant.SemanticApi
import Itasca.Generated.FunsInstantiate
import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Spec.FloatTrunc
import Itasca.Runtime.Store.Api.TableInitLists
import Itasca.Runtime.Store.Invariant.Typing
import Itasca.Runtime.Store.Initialization.SegmentReady
import Itasca.Runtime.Spec.FloatPromote
import Itasca.Runtime.Store.Preparation.PreparationCalls
import Itasca.Runtime.Store.Api.DefineTable
import Itasca.Runtime.Store.Invariant.PrecommitError
import Itasca.Runtime.Compiler.Local.Initializer.InitializerElementAppend
import Itasca.Runtime.Store.Api.MemoryBindingLoop
import Itasca.Runtime.Representation.StoreCapacity
import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
import Itasca.Runtime.Compiler.Local.Initializer

/-!
Sections, each formerly its own module: TableInit, MemoryInit, MemoryAllocationCauses, NewMemoryCauses, MemoryStagingCauses, TableAllocationCauses, NewTableCauses, TableStagingCauses, GrowthEffects, GrowthLimits.
-/

/-! ## TableInit -/

section

/-!
Table initialization source decoding and handler refinement. Shared segment-copy list algebra remains separate for memory and table copy consumers.
-/

/-! ## Table Init Semantics -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt

theorem table_init_decodes {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (tableIndex elementIndex : U32) (tableAddress : runtime.TableAddr) (elementAddress : Usize)
    (table : runtime.store.TableInst) (segment : runtime.store.ElemInst)
    (destination source count : Nat) (words : alloc.vec.Vec U64)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (tableMapped : inst.tables.val[tableIndex.val]? = some tableAddress)
    (elementMapped : inst.elems.val[elementIndex.val]? = some elementAddress)
    (target : store.tables.val[tableAddress.index.val]? = some table)
    (resolved : store.elems.val[elementAddress.val]? = some segment)
    (sameType : table.ty = segment.ty)
    (inside : source+count ≤ segment.refs.length)
    (copied : words.val = copySegment table.elements.val segment.refs.val destination source count) :
    decodeStore view code {store with tables := store.tables.set tableAddress.index {table with elements := words}} =
      Spec.Segment.tableInit (decodeStore view code store) ambient tableIndex.val elementIndex.val destination source count := by
  have tableRead : ambient.MODULE.TABLES[tableIndex.val]! = tableAddress.index.val := by
    rw [moduleEq]
    simp [decodeInstance,List.getElem!_eq_getElem?_getD,tableMapped]
  have elementRead : fun_elem ⟨decodeStore view code store,ambient⟩ (.mk_uN elementIndex.val) = decodeElement segment := by
    simp [fun_elem,moduleEq,decodeInstance,decodeStore,proj_uN_0,List.getElem!_eq_getElem?_getD,elementMapped,resolved]
  have lengthEq : words.length = table.elements.length := by
    simpa only [alloc.vec.Vec.length] using (congrArg List.length copied).trans (copy_segment_length _ _ _ _ _)
  have refsEq : words.val.map (decodeRef table.ty) =
      Spec.Segment.copyInto (table.elements.val.map (decodeRef table.ty))
        (segment.refs.val.map (decodeRef segment.ty)) destination source count := by
    rw [copied,copy_segment_eq_copy_into,copy_into_map _ _ _ _ _ _ inside,sameType]
  have lists := Itasca.Runtime.Representation.map_set_modify decodeTable
    (fun t => {t with REFS := Spec.Segment.copyInto t.REFS (decodeElement segment).REFS destination source count})
    store.tables.val tableAddress.index.val table {table with elements := words} target
    (by simp only [decodeTable,decodeElement,lengthEq,refsEq])
  rw [Spec.Segment.table_init_eq,tableRead,elementRead]
  unfold decodeStore
  simp only [alloc.vec.Vec.set_val_eq,lists]
  rfl

/-- The four segment instructions either finish or reduce to a source trap. -/
def segmentResult (status : core.result.Result Unit runtime.ExecError) : List admininstr :=
  match status with | .Ok _ => [] | .Err _ => [.TRAP]

theorem TableInitializationEffect.refines {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (tableIndex elementIndex : U32) (tableAddress : runtime.TableAddr) (elementAddress : Usize)
    (table : runtime.store.TableInst) (segment : runtime.store.ElemInst)
    (destination source count : U64) (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M)
    (effect : TableInitializationEffect store tableAddress.index table segment destination source count out)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (tableMapped : inst.tables.val[tableIndex.val]? = some tableAddress)
    (elementMapped : inst.elems.val[elementIndex.val]? = some elementAddress)
    (target : store.tables.val[tableAddress.index.val]? = some table)
    (resolved : store.elems.val[elementAddress.val]? = some segment)
    (sameType : table.ty = segment.ty)
    (shape : Shape view store) (sourceSyntax : StoreSyntax code store) (ambientWf : wf_frame ambient)
    (elementBound : segment.refs.length < 2^32)
    (dstBound : destination.val < 2^32) (srcBound : source.val < 2^32) (countBound : count.val < 2^32) :
    StepsH ⟨⟨decodeStore view code store,ambient⟩,Spec.Segment.operands destination.val source.val count.val ++
      [.TABLE_INIT (.mk_uN tableIndex.val) (.mk_uN elementIndex.val)]⟩ []
      ⟨⟨decodeStore view code out.2,ambient⟩,segmentResult out.1⟩ := by
  have tableRead : fun_table ⟨decodeStore view code store,ambient⟩ (.mk_uN tableIndex.val) = decodeTable table := by
    simp [fun_table,moduleEq,decodeInstance,decodeStore,proj_uN_0,List.getElem!_eq_getElem?_getD,tableMapped,target]
  have elementRead : fun_elem ⟨decodeStore view code store,ambient⟩ (.mk_uN elementIndex.val) = decodeElement segment := by
    simp [fun_elem,moduleEq,decodeInstance,decodeStore,proj_uN_0,List.getElem!_eq_getElem?_getD,elementMapped,resolved]
  have wf := decode_store_wf view code store shape sourceSyntax
  unfold TableInitializationEffect at effect
  split at effect
  · rename_i inside
    obtain ⟨words,rfl,copied⟩ := effect
    simp only [segmentResult]
    rw [table_init_decodes view code store inst ambient tableIndex elementIndex tableAddress elementAddress
      table segment destination.val source.val count.val words moduleEq tableMapped elementMapped target resolved sameType inside.2 copied]
    apply Spec.Segment.table_init_steps _ _ _ _ _ _ _ wf ambientWf dstBound srcBound countBound
      (by scalar_tac) (by scalar_tac)
    · simpa [moduleEq,decodeInstance] using (List.getElem?_eq_some_iff.mp tableMapped).1
    · have addressRead : ambient.MODULE.TABLES[tableIndex.val]! = tableAddress.index.val := by
        simp [moduleEq,decodeInstance,List.getElem!_eq_getElem?_getD,tableMapped]
      rw [addressRead]
      simpa [decodeStore] using (List.getElem?_eq_some_iff.mp target).1
    · rw [tableRead]
      have bound := (shape.tables table (List.mem_of_getElem? target)).1
      simp only [decodeTable,List.length_map]
      scalar_tac
    · simpa [elementRead,decodeElement] using elementBound
    · simpa [tableRead,elementRead,decodeTable,decodeElement] using And.intro inside.2 inside.1
  · rename_i outside
    rw [effect]
    apply Spec.steps_h_single
    apply Spec.Segment.table_init_trap _ _ _ _ _ _ _ wf ambientWf dstBound srcBound countBound
      (by scalar_tac) (by scalar_tac)
    simp only [tableRead,elementRead,decodeTable,decodeElement,List.length_map]
    simp only [alloc.vec.Vec.length] at outside
    omega

end Itasca.Runtime.Store

end

/-! ## Table Init Execution -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt

theorem bulk_table_init_refines {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (sourceCode : CodeInterpretation)
    (store : runtime.store.Store M) (instIndex function : Usize) (slots : Slice U64)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (entry element tableId : U32) (address : Usize) (tableAddress : runtime.TableAddr)
    (table : runtime.store.TableInst) (segment : runtime.store.ElemInst)
    (destination source count : U64) (ambient : frame)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some compiled)
    (descriptor : compiled.indirect.val[entry.val]? = some (element, tableId))
    (mapped : inst.elems.val[element.val]? = some address)
    (resolved : store.elems.val[address.val]? = some segment)
    (tableMapped : inst.tables.val[tableId.val]? = some tableAddress)
    (target : store.tables.val[tableAddress.index.val]? = some table)
    (destinationSlot : slots.val[0]? = some destination)
    (sourceSlot : slots.val[1]? = some source) (countSlot : slots.val[2]? = some count)
    (sameType : table.ty = segment.ty) (shape : Shape view store)
    (sourceSyntax : StoreSyntax sourceCode store) (ambientWf : wf_frame ambient)
    (moduleEq : ambient.MODULE = decodeInstance store inst) (elementBound : segment.refs.length < 2^32) :
    runtime.interp.bulk.execute memory store instIndex function 0#usize slots (.TableInit 0#u32 entry)
      ⦃ out => StepsH ⟨⟨decodeStore view sourceCode store,ambient⟩,
        Spec.Segment.operands (bulkWord destination).val (bulkWord source).val (bulkWord count).val ++
          [.TABLE_INIT (.mk_uN tableId.val) (.mk_uN element.val)]⟩ []
        ⟨⟨decodeStore view sourceCode out.2,ambient⟩,segmentResult out.1⟩ ⦄ := by
  apply WP.spec_mono (bulk_table_init memory store instIndex function slots inst compiled entry element tableId
    address tableAddress table segment destination source count found functionFound descriptor mapped resolved
    tableMapped target destinationSlot sourceSlot countSlot)
  intro out effect
  exact effect.refines view sourceCode store inst ambient tableId element tableAddress address table segment
    (bulkWord destination) (bulkWord source) (bulkWord count) out moduleEq tableMapped mapped target resolved
    sameType shape sourceSyntax ambientWf elementBound (by scalar_tac) (by scalar_tac) (by scalar_tac)

end Itasca.Runtime.Store

end

end

/-! ## MemoryInit -/

section

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
    rw [copied,←Spec.Segment.copy_into_eq_set_slice _ _ _ _ _ inside.1 inside.2]
    exact copy_into_map _ _ _ _ _ _ inside.1
  have lists := Itasca.Runtime.Representation.map_set_modify (decodeMemory view)
    (fun m => {m with BYTES := Spec.Segment.copyInto m.BYTES (decodeData segment).BYTES destination source count})
    store.memories.val memoryAddress.index.val memory {memory with buf := buffer} target
    (by simp only [decodeMemory,decodeData,lengthEq,bytesEq])
  have addressBound : ambient.MODULE.MEMS[0]! < (decodeStore view code store).MEMS.length := by
    rw [memoryRead]
    simpa [decodeStore] using (List.getElem?_eq_some_iff.mp target).1
  rw [Spec.Segment.memory_init_eq _ _ _ _ _ _ addressBound
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
  have wf := decode_store_wf view code store shape sourceSyntax
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
      exact decode_bytes_wf segment.bytes.val
    · simpa [memoryRead,dataRead,decodeMemory,decodeData,decodeBytes] using And.intro inside.2 inside.1
  · rename_i outside
    rw [effect]
    apply Spec.steps_h_single
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

end

/-! ## MemoryAllocationCauses -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

def MemoryAllocationCause {M A : Type} (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) (ty : Itasca.wasm_types.MemType) : runtime.ResourceLimit → Prop
  | .Objects => store.limits.max_objects.val ≤ objectCount store
  | .Allocation =>
      store.limits.max_memory_bytes.val < store.memory_bytes.val + ty.limits.min.val * 65536 ∨
      allocator.reserve store.memories 1#usize = .ok (false,store.memories)
  | _ => False

/-- A memory-definition resource failure retains its actual source-sized byte
budget comparison or the exact memory-vector allocator refusal. -/
theorem define_memory_resource_causes {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (ty : Itasca.wasm_types.MemType) (buffer : M)
    (bound : objectCount store ≤ Usize.max) :
    runtime.store.Store.define_memory_with memory allocator store ty buffer ⦃ out => ∀ limit,
      out.1 = .Err (.Exhausted limit) → out.2 = store ∧ MemoryAllocationCause allocator store ty limit ⦄ := by
  unfold runtime.store.Store.define_memory_with
  step with room_spec memory store bound as ⟨room,roomEq⟩
  rw [roomEq]
  split
  · rename_i space
    simp [core.result.Result.Insts.CoreOpsTry.branch]
    step with check_limits_spec ty.limits 65536#u32 as ⟨limits,limitsEq⟩
    rw [limitsEq]
    by_cases fitted : LimitsFit ty.limits 65536#u32
    · simp only [if_pos fitted]
      simp [core.result.Result.Insts.CoreOpsTry.branch,lift]
      step as ⟨size,sizeEq⟩
      rw [laws.read]
      simp [lift]
      by_cases length : (view buffer).length = size.val
      · simp only [length,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
        have bytes : (view buffer).length=ty.limits.min.val*65536 := by scalar_tac
        step with within_spec store.memory_bytes (Slice.len (view buffer)) store.limits.max_memory_bytes as ⟨fits,fitsEq⟩
        rw [fitsEq]
        split
        · rename_i total
          have total' : store.memory_bytes.val+(view buffer).length≤store.limits.max_memory_bytes.val := by simpa using total
          obtain ⟨answer,wrapped,called⟩ := reserve_with_cause allocator law store.memories 1#usize
          rw [wrapped]
          cases answer
          · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,MemoryAllocationCause,called]
          · simp
            have room : store.memories.length < Usize.max := by unfold objectCount at space; scalar_tac
            step
            have sizeBound : size.val≤Usize.max := by scalar_tac
            have castEq := cast_usize_exact size sizeBound
            step
            simp
        · simp [MemoryAllocationCause]
          exact Or.inl (by scalar_tac)
      · simp [length]
    · simp [fitted,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,MemoryAllocationCause]
    omega
end Itasca.Runtime.Store

end

/-! ## NewMemoryCauses -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

def NewMemoryResourceCause {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (store : runtime.store.Store M)
    (ty : Itasca.wasm_types.MemType) (limit : runtime.ResourceLimit) : Prop :=
  MemoryAllocationCause allocator store ty limit ∨
    (limit = .Allocation ∧ (Usize.max < ty.limits.min.val * 65536 ∨
      ∃ requested : Usize, requested.val = ty.limits.min.val * 65536 ∧
        memory.new_zeroed requested = .ok none))

/-- The actual new-memory path exposes size overflow, configured byte-budget
failure, a refused zeroed buffer, or the definition's exact resource cause. -/
theorem add_memory_resource_cause {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : Usize)
    (ty : Itasca.wasm_types.MemType)
    (found : inst.module.module.env.mem_types.val[index.val]? = some ty)
    (bound : objectCount store ≤ Usize.max)
    (limit : runtime.ResourceLimit) (after : runtime.store.Store M) (next : runtime.store.ModuleInst)
    (run : runtime.store.instantiate.Store.add_instance_memory memory allocator store inst index =
      .ok (.Err (.Exhausted limit),after,next)) :
    after = store ∧ next = inst ∧ NewMemoryResourceCause memory allocator store ty limit := by
  have multiply : (UScalar.cast .U64 ty.limits.min) * 65536#u64
      ⦃ size => size.val = ty.limits.min.val * 65536 ⦄ := by
    step as ⟨size,sizeValue⟩
    scalar_tac
  obtain ⟨size,sizeRun,sizeValue⟩ := WP.spec_imp_exists multiply
  unfold runtime.store.instantiate.Store.add_instance_memory at run
  simp only [runtime.compiler.ExecutableModule.env.eq,Itasca.metadata.Module.impl.env,Itasca.metadata.Env.impl.mem_types,bind_ok] at run
  rw [Compiler.initializer_slice_index inst.module.module.env.mem_types.deref index ty
    (by simpa [alloc.vec.Vec.deref] using found)] at run
  simp only [bind_ok,lift,sizeRun] at run
  have maxCast : (UScalar.cast .U64 core.num.Usize.MAX).val = Usize.max := by
    rw [UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    change Usize.max < 18446744073709551616
    rcases Usize.bounds_eq with same | same <;> simp [same,U32.max_eq,U64.max_eq]
  split at run
  · simp only [Result.ok.injEq,Prod.mk.injEq,core.result.Result.Err.injEq,runtime.ExecError.Exhausted.injEq] at run
    obtain ⟨rfl,rfl,rfl⟩ := run
    exact ⟨rfl,rfl,Or.inr ⟨rfl,Or.inl (by scalar_tac)⟩⟩
  · have sized : size.val ≤ Usize.max := by scalar_tac
    have castEq := cast_usize_exact size sized
    obtain ⟨fits,fitsRun,fitsEq⟩ := WP.spec_imp_exists
      (within_spec store.memory_bytes (UScalar.cast .Usize size) store.limits.max_memory_bytes)
    rw [fitsRun] at run
    simp only [bind_ok] at run
    split at run
    · obtain ⟨buffer,created,contents⟩ := WP.spec_imp_exists (laws.create (UScalar.cast .Usize size))
      rw [created] at run
      simp only [bind_ok] at run
      cases buffer with
      | none =>
        simp only [Result.ok.injEq,Prod.mk.injEq,core.result.Result.Err.injEq,runtime.ExecError.Exhausted.injEq] at run
        obtain ⟨rfl,rfl,rfl⟩ := run
        exact ⟨rfl,rfl,Or.inr ⟨rfl,Or.inr ⟨UScalar.cast .Usize size,by scalar_tac,created⟩⟩⟩
      | some buffer =>
        simp only [] at run
        obtain ⟨⟨status,changed⟩,defined,cause⟩ := WP.spec_imp_exists
          (define_memory_resource_causes memory allocator law view laws store ty buffer bound)
        rw [defined] at run
        simp only [bind_ok] at run
        cases status with
        | Ok address =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,bind_tc_ok,uncurry_apply_pair] at run
          obtain ⟨pushed,pushRun,impossible⟩ := normal_bind_exists _ _ _ run
          simp only [Result.ok.injEq,Prod.mk.injEq] at impossible
          cases impossible.1
        | Err error =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,core.convert.FromSame.from] at run
          simp only [bind_ok,bind_tc_ok,uncurry_apply_pair,Result.ok.injEq,Prod.mk.injEq,core.result.Result.Err.injEq] at run
          obtain ⟨rfl,rfl,rfl⟩ := run
          obtain ⟨same,cause⟩ := cause limit rfl
          exact ⟨same,rfl,Or.inl cause⟩
    · simp only [Result.ok.injEq,Prod.mk.injEq,core.result.Result.Err.injEq,runtime.ExecError.Exhausted.injEq] at run
      obtain ⟨rfl,rfl,rfl⟩ := run
      refine ⟨rfl,rfl,Or.inl (Or.inl ?_)⟩
      have failed : ¬store.memory_bytes.val+(UScalar.cast .Usize size).val≤store.limits.max_memory_bytes.val := by
        simpa [fitsEq] using ‹¬fits=true›
      scalar_tac
end Itasca.Runtime.Store

end

/-! ## MemoryStagingCauses -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

abbrev memoryStageCall {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (state : runtime.store.Store M × runtime.store.ModuleInst) (index : Usize) :=
  runtime.store.instantiate.Store.add_instance_memory memory allocator state.1 state.2 index

def MemoryStagingCause {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (store : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (start : Usize) (limit : runtime.ResourceLimit) : Prop :=
  ∃ current currentInst index ty,
    PreparationCalls (memoryStageCall memory allocator) (store,inst) start (current,currentInst) index ∧
    currentInst.module.module.env.mem_types.val[index.val]? = some ty ∧
    runtime.store.instantiate.Store.add_instance_memory memory allocator current currentInst index = .ok (.Err (.Exhausted limit),current,currentInst) ∧
    NewMemoryResourceCause memory allocator current ty limit

/-- The actual memory allocation loop establishes complete issued memory maps,
while retaining all old store objects and all other provisional maps. -/
theorem memory_staging_resource_loop {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (before store : runtime.store.Store M) (seed inst : runtime.store.ModuleInst)
    (start : Usize)
    (startBound : start.val ≤ seed.module.module.env.mem_types.val.length)
    (changed : store = {before with memories := store.memories, memory_bytes := store.memory_bytes})
    (instChanged : inst = {seed with memories := inst.memories})
    (retained : StagedPrefix before store) (objectBound : objectCount store ≤ Usize.max)
    (issued : ∀ address ∈ inst.memories.val, address.index.val < store.memories.length)
    (count : inst.memories.length = start.val)
    :
    runtime.store.instantiate.Store.prepare_instance_loop6 memory allocator store (.Ok ()) start inst
      ⦃ out => ∃ after next status, out = typeParts after status next ∧
        after = {before with memories := after.memories, memory_bytes := after.memory_bytes} ∧ next = {seed with memories := next.memories} ∧
        StagedPrefix before after ∧ objectCount after ≤ Usize.max ∧
        (∀ address ∈ next.memories.val, address.index.val < after.memories.length) ∧
        (status = .Ok () → next.memories.length = seed.module.module.env.mem_types.val.length) ∧
        (∀ limit, status = .Err (.Exhausted limit) → MemoryStagingCause memory allocator store inst start limit) ⦄ := by
  have capacity := seed.module.module.env.mem_types.property
  unfold runtime.store.instantiate.Store.prepare_instance_loop6
  apply loop.spec_decr_nat (fun state => seed.module.module.env.mem_types.val.length - state.2.2.1.val)
    (fun state => state.1 = {before with memories := state.1.memories, memory_bytes := state.1.memory_bytes} ∧
      state.2.2.2 = {seed with memories := state.2.2.2.memories} ∧ StagedPrefix before state.1 ∧
      objectCount state.1 ≤ Usize.max ∧
      (∀ address ∈ state.2.2.2.memories.val, address.index.val < state.1.memories.length) ∧
      state.2.2.1.val ≤ seed.module.module.env.mem_types.val.length ∧
      (state.2.1 = .Ok () → state.2.2.2.memories.length = state.2.2.1.val) ∧
      (state.2.1 = .Ok () → PreparationCalls (memoryStageCall memory allocator) (store,inst) start (state.1,state.2.2.2) state.2.2.1) ∧
      (∀ limit, state.2.1 = .Err (.Exhausted limit) → MemoryStagingCause memory allocator store inst start limit))
  · rintro ⟨current, status, index, currentInst⟩ ⟨currentChanged, mapChanged, prefixStore, bound, currentIssued, indexBound, counting, trace, cause⟩
    dsimp only at currentChanged mapChanged prefixStore bound currentIssued indexBound counting ⊢
    have source : currentInst.module = seed.module := by
      have eq := congrArg runtime.store.ModuleInst.module mapChanged
      exact eq
    unfold runtime.store.instantiate.Store.prepare_instance_loop6.body
    simp only [runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.mem_types, source, bind_ok]
    split
    · rename_i more
      have within : index.val < seed.module.module.env.mem_types.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, currentInst, .Err error, by simp [typeParts, source], currentChanged,
          mapChanged, prefixStore, bound, currentIssued, by simp, cause⟩
      | Ok value =>
        cases value
        have size := counting rfl
        have actualBound : index.val < currentInst.module.module.env.mem_types.val.length := by simpa only [source] using within
        have room : currentInst.memories.length < Usize.max := by omega
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        have reached := trace rfl
        obtain ⟨⟨status,after,nextInst⟩,called,effect⟩ := WP.spec_imp_exists
          (add_instance_memory_effect memory allocator law view laws current currentInst index actualBound bound room)
        rw [called]
        simp only [bind_ok,uncurry_apply_pair]
        obtain ⟨afterChanged, nextChanged, prefixNext, nextBound⟩ := effect.context bound
        have afterExact : after = {before with memories := after.memories, memory_bytes := after.memory_bytes} := by
          calc
            after = {current with memories := after.memories, memory_bytes := after.memory_bytes} := afterChanged
            _ = _ := by rw [currentChanged]
        have nextExact : nextInst = {seed with memories := nextInst.memories} := by
          calc
            nextInst = {currentInst with memories := nextInst.memories} := nextChanged
            _ = _ := by rw [mapChanged]
        step as ⟨next, increment⟩
        refine ⟨afterExact, nextExact, prefixStore.trans prefixNext, nextBound,
          effect.issued currentIssued, ?_, ?_, ?_, ?_, ?_⟩
        · omega
        · intro success
          have appended := effect.count success
          dsimp only at appended
          omega
        · intro success
          subst status
          exact .next reached called increment
        · intro limit rejected
          subst status
          let ty := currentInst.module.module.env.mem_types.val[index.val]
          have found : currentInst.module.module.env.mem_types.val[index.val]? = some ty := List.getElem?_eq_getElem actualBound
          obtain ⟨unchanged,sameInst,refusal⟩ :=
            add_memory_resource_cause memory allocator law view laws current currentInst index ty found bound limit after nextInst called
          subst after
          subst nextInst
          exact ⟨current,currentInst,index,ty,reached,found,called,refusal⟩
        · omega
    · rename_i stopped
      have atEnd : index.val = seed.module.module.env.mem_types.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      refine ⟨current, currentInst, status, by simp [typeParts, source], currentChanged,
        mapChanged, prefixStore, bound, currentIssued, ?_, cause⟩
      intro success
      simpa only [atEnd] using counting success
  · exact ⟨changed, instChanged, retained, objectBound, issued, startBound, (fun _ => count), (fun _ => .refl _ _), by simp⟩

end Itasca.Runtime.Store

end

/-! ## TableAllocationCauses -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

def TableAllocationCause {M A : Type} (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) (ty : Itasca.wasm_types.TableType) : runtime.ResourceLimit → Prop
  | .Objects => store.limits.max_objects.val ≤ objectCount store
  | .Allocation =>
      store.limits.max_table_elements.val < store.table_elements.val + ty.limits.min.val ∨
      allocator.reserve (alloc.vec.Vec.new U64) (UScalar.cast .Usize ty.limits.min) =
        .ok (false,alloc.vec.Vec.new U64) ∨
      allocator.reserve store.tables 1#usize = .ok (false,store.tables)
  | _ => False

theorem define_table_resource_causes {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (ty : Itasca.wasm_types.TableType)
    (bound : objectCount store ≤ Usize.max) :
    runtime.store.Store.define_table_with memory allocator store ty ⦃ out => ∀ limit,
      out.1 = .Err (.Exhausted limit) → out.2 = store ∧ TableAllocationCause allocator store ty limit ⦄ := by
  unfold runtime.store.Store.define_table_with
  step with room_spec memory store bound as ⟨room,roomEq⟩
  rw [roomEq]
  split
  · rename_i space
    simp [core.result.Result.Insts.CoreOpsTry.branch]
    step with check_limits_spec ty.limits core.num.U32.MAX as ⟨limits,limitsEq⟩
    rw [limitsEq]
    by_cases fitted : LimitsFit ty.limits core.num.U32.MAX
    · simp [fitted,core.result.Result.Insts.CoreOpsTry.branch,lift]
      step with within_spec store.table_elements (UScalar.cast .Usize ty.limits.min)
        store.limits.max_table_elements as ⟨fits,fitsEq⟩
      rw [fitsEq]
      split
      · rename_i total
        have total' : store.table_elements.val+ty.limits.min.val≤store.limits.max_table_elements.val := by scalar_tac
        obtain ⟨answer,wrapped,called⟩ := reserve_with_cause allocator law (alloc.vec.Vec.new U64) (UScalar.cast .Usize ty.limits.min)
        rw [wrapped]
        cases answer
        · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,TableAllocationCause,called]
        · simp
          step with define_table_loop ty.limits.min (alloc.vec.Vec.new U64) 0#u32 (by simp) (by scalar_tac) as ⟨elements,contents⟩
          obtain ⟨answer,wrapped,called⟩ := reserve_with_cause allocator law store.tables 1#usize
          rw [wrapped]
          cases answer
          · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,TableAllocationCause,called]
          · simp
            have room : store.tables.length < Usize.max := by unfold objectCount at space; scalar_tac
            step
            step
            simp
      · simp [TableAllocationCause]
        exact Or.inl (by scalar_tac)
    · simp [fitted,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,TableAllocationCause]
    omega
end Itasca.Runtime.Store

end

/-! ## NewTableCauses -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The actual table staging helper propagates the exact declared table's
quota or allocation refusal before changing either map or store. -/
theorem add_table_resource_cause {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : Usize)
    (ty : Itasca.wasm_types.TableType) (found : inst.module.module.env.table_types.val[index.val]? = some ty)
    (bound : objectCount store ≤ Usize.max)
    (limit : runtime.ResourceLimit) (after : runtime.store.Store M) (next : runtime.store.ModuleInst)
    (run : runtime.store.instantiate.Store.add_instance_table memory allocator store inst index = .ok (.Err (.Exhausted limit),after,next)) :
    after = store ∧ next = inst ∧ TableAllocationCause allocator store ty limit := by
  unfold runtime.store.instantiate.Store.add_instance_table at run
  simp only [runtime.compiler.ExecutableModule.env.eq,Itasca.metadata.Module.impl.env,Itasca.metadata.Env.impl.table_types,bind_ok] at run
  rw [Compiler.initializer_slice_index inst.module.module.env.table_types.deref index ty
    (by simpa [alloc.vec.Vec.deref] using found),bind_ok] at run
  obtain ⟨⟨status,staged⟩,defined,run⟩ := normal_bind_exists _ _ _ run
  have effect := define_table_resource_causes memory allocator law store ty bound
  rw [defined,WP.spec_ok] at effect
  cases status with
  | Ok address =>
    simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at run
    obtain ⟨addresses,pushed,run⟩ := normal_bind_exists _ _ _ run
    simp at run
  | Err rejected =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
    obtain ⟨rfl,rfl,rfl⟩ := run
    obtain ⟨same,cause⟩ := effect limit rfl
    exact ⟨same,rfl,cause⟩
end Itasca.Runtime.Store

end

/-! ## TableStagingCauses -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

abbrev tableStageCall {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (state : runtime.store.Store M × runtime.store.ModuleInst) (index : Usize) :=
  runtime.store.instantiate.Store.add_instance_table memory allocator state.1 state.2 index

def TableStagingCause {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (store : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (start : Usize) (limit : runtime.ResourceLimit) : Prop :=
  ∃ current currentInst index ty,
    PreparationCalls (tableStageCall memory allocator) (store,inst) start (current,currentInst) index ∧
    currentInst.module.module.env.table_types.val[index.val]? = some ty ∧
    runtime.store.instantiate.Store.add_instance_table memory allocator current currentInst index = .ok (.Err (.Exhausted limit),current,currentInst) ∧
    TableAllocationCause allocator current ty limit

/-- The actual table allocation loop establishes complete issued table maps,
while retaining all old store objects and all other provisional maps. -/
theorem table_staging_resource_loop {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (seed inst : runtime.store.ModuleInst)
    (start : Usize)
    (startBound : start.val ≤ seed.module.module.env.table_types.val.length)
    (changed : store = {before with tables := store.tables, table_elements := store.table_elements})
    (instChanged : inst = {seed with tables := inst.tables})
    (retained : StagedPrefix before store) (objectBound : objectCount store ≤ Usize.max)
    (issued : ∀ address ∈ inst.tables.val, address.index.val < store.tables.length)
    (count : inst.tables.length = start.val)
    :
    runtime.store.instantiate.Store.prepare_instance_loop5 memory allocator store (.Ok ()) start inst
      ⦃ out => ∃ after next status, out = typeParts after status next ∧
        after = {before with tables := after.tables, table_elements := after.table_elements} ∧ next = {seed with tables := next.tables} ∧
        StagedPrefix before after ∧ objectCount after ≤ Usize.max ∧
        (∀ address ∈ next.tables.val, address.index.val < after.tables.length) ∧
        (status = .Ok () → next.tables.length = seed.module.module.env.table_types.val.length) ∧
        (∀ limit, status = .Err (.Exhausted limit) → TableStagingCause memory allocator store inst start limit) ⦄ := by
  have capacity := seed.module.module.env.table_types.property
  unfold runtime.store.instantiate.Store.prepare_instance_loop5
  apply loop.spec_decr_nat (fun state => seed.module.module.env.table_types.val.length - state.2.2.1.val)
    (fun state => state.1 = {before with tables := state.1.tables, table_elements := state.1.table_elements} ∧
      state.2.2.2 = {seed with tables := state.2.2.2.tables} ∧ StagedPrefix before state.1 ∧
      objectCount state.1 ≤ Usize.max ∧
      (∀ address ∈ state.2.2.2.tables.val, address.index.val < state.1.tables.length) ∧
      state.2.2.1.val ≤ seed.module.module.env.table_types.val.length ∧
      (state.2.1 = .Ok () → state.2.2.2.tables.length = state.2.2.1.val) ∧
      (state.2.1 = .Ok () → PreparationCalls (tableStageCall memory allocator) (store,inst) start (state.1,state.2.2.2) state.2.2.1) ∧
      (∀ limit, state.2.1 = .Err (.Exhausted limit) → TableStagingCause memory allocator store inst start limit))
  · rintro ⟨current, status, index, currentInst⟩ ⟨currentChanged, mapChanged, prefixStore, bound, currentIssued, indexBound, counting, trace, cause⟩
    dsimp only at currentChanged mapChanged prefixStore bound currentIssued indexBound counting ⊢
    have source : currentInst.module = seed.module := by
      have eq := congrArg runtime.store.ModuleInst.module mapChanged
      exact eq
    unfold runtime.store.instantiate.Store.prepare_instance_loop5.body
    simp only [runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.table_types, source, bind_ok]
    split
    · rename_i more
      have within : index.val < seed.module.module.env.table_types.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, currentInst, .Err error, by simp [typeParts, source], currentChanged,
          mapChanged, prefixStore, bound, currentIssued, by simp, cause⟩
      | Ok value =>
        cases value
        have size := counting rfl
        have actualBound : index.val < currentInst.module.module.env.table_types.val.length := by simpa only [source] using within
        have room : currentInst.tables.length < Usize.max := by omega
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        have reached := trace rfl
        obtain ⟨⟨status,after,nextInst⟩,called,effect⟩ := WP.spec_imp_exists
          (add_instance_table_effect memory allocator law current currentInst index actualBound bound room)
        rw [called]
        simp only [bind_ok,uncurry_apply_pair]
        obtain ⟨afterChanged, nextChanged, prefixNext, nextBound⟩ := effect.context bound
        have afterExact : after = {before with tables := after.tables, table_elements := after.table_elements} := by
          calc
            after = {current with tables := after.tables, table_elements := after.table_elements} := afterChanged
            _ = _ := by rw [currentChanged]
        have nextExact : nextInst = {seed with tables := nextInst.tables} := by
          calc
            nextInst = {currentInst with tables := nextInst.tables} := nextChanged
            _ = _ := by rw [mapChanged]
        step as ⟨next, increment⟩
        refine ⟨afterExact, nextExact, prefixStore.trans prefixNext, nextBound,
          effect.issued currentIssued, ?_, ?_, ?_, ?_, ?_⟩
        · omega
        · intro success
          have appended := effect.count success
          dsimp only at appended
          omega
        · intro success
          subst status
          exact .next reached called increment
        · intro limit rejected
          subst status
          let ty := currentInst.module.module.env.table_types.val[index.val]
          have found : currentInst.module.module.env.table_types.val[index.val]? = some ty := List.getElem?_eq_getElem actualBound
          obtain ⟨unchanged,sameInst,refusal⟩ :=
            add_table_resource_cause memory allocator law current currentInst index ty found bound limit after nextInst called
          subst after
          subst nextInst
          exact ⟨current,currentInst,index,ty,reached,found,called,refusal⟩
        · omega
    · rename_i stopped
      have atEnd : index.val = seed.module.module.env.table_types.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      refine ⟨current, currentInst, status, by simp [typeParts, source], currentChanged,
        mapChanged, prefixStore, bound, currentIssued, ?_, cause⟩
      intro success
      simpa only [atEnd] using counting success
  · exact ⟨changed, instChanged, retained, objectBound, issued, startBound, (fun _ => count), (fun _ => .refl _ _), by simp⟩

end Itasca.Runtime.Store

end

/-! ## GrowthEffects -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
/-- The retained raw growth effect suffices to preserve shape, independently
of the handler that produced it. -/
theorem MemoryGrowth.shape {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) (hs : Shape view s) (index : Usize) (delta : U32)
    (hindex : index.val < s.memories.length) (result : U32 × runtime.store.Store M)
    (effect : MemoryGrowth view code s index delta result) : Shape view result.2 := by
  rcases effect with ⟨_, _, frame⟩ | ⟨old, after, count, hlookup, hbytes, hcount, hlimit, hpages, hmaximum, _, hresult⟩
  · rcases frame with unchanged | ⟨old, after, hlookup, hview, hresult⟩
    · simpa [unchanged] using hs
    · have hold : old = s.memories.val[index.val] := by
        simp only [List.getElem?_eq_getElem hindex, Option.some.injEq] at hlookup
        exact hlookup.symm
      rw [hresult]
      apply hs.memory_replace_same_length index hindex _
      · simp [hview, hold]
      · simp [hold]
  · have hold : old = s.memories.val[index.val] := by
      simp only [List.getElem?_eq_getElem hindex, Option.some.injEq] at hlookup
      exact hlookup.symm
    have hbefore := hs.memories old (List.mem_of_getElem? hlookup)
    have hlength : (view after).length = (view old.buf).length + delta.val * 65536 := by
      simpa using congrArg List.length hbytes
    have hpageEq : (view after).length / 65536 = (view old.buf).length / 65536 + delta.val := by omega
    have hmemory : MemoryShape view {old with buf := after} := by
      refine ⟨?_, ?_, ?_⟩
      · have halign := hbefore.1
        simp only [Slice.length] at *
        omega
      · simpa [hpageEq] using hpages
      · intro maximum hmax
        change old.maximum = some maximum at hmax
        have hmaxBefore := hbefore.2.2 maximum hmax
        constructor
        · simp only [hmax, core.option.Option.unwrap_or] at hmaximum
          simpa [hpageEq] using hmaximum
        · exact hmaxBefore.2
    rw [hresult]
    apply hs.memory_extend index hindex _ hmemory (delta.val * 65536) ?_ count hcount hlimit
    simpa [hold] using hlength

theorem TableGrowth.shape {M : Type} (view : M → Slice U8)
    (s : runtime.store.Store M) (hs : Shape view s) (index : Usize) (delta : U32) (value : U64)
    (hindex : index.val < s.tables.length) (hv : ReferenceShape s (s.tables.val[index.val]).ty value)
    (result : U32 × runtime.store.Store M) (effect : TableGrowth s index delta value result) : Shape view result.2 := by
  rcases effect with unchanged | ⟨old, elements, count, hlookup, hvalues, hmax, hcount, hlimit, hmaximum, hresult⟩
  · simpa [unchanged.2] using hs
  · have hold : old = s.tables.val[index.val] := by
      simp only [List.getElem?_eq_getElem hindex, Option.some.injEq] at hlookup
      exact hlookup.symm
    have hbefore := hs.tables old (List.mem_of_getElem? hlookup)
    have hlength : elements.length = old.elements.length + delta.val := by
      simpa using congrArg List.length hvalues
    have htable : TableShape s {old with elements} := by
      refine ⟨?_, ?_, ?_⟩
      · simpa [hlength] using hmax
      · intro maximum hdeclared
        change old.maximum = some maximum at hdeclared
        simp only [hdeclared, core.option.Option.unwrap_or] at hmaximum
        simpa [hlength] using hmaximum
      · intro word hword
        change word ∈ elements.val at hword
        rw [hvalues] at hword
        rcases List.mem_append.mp hword with before | added
        · exact hbefore.2.2 word before
        · have heq := List.eq_of_mem_replicate added
          subst word
          simpa [hold] using hv
    rw [hresult]
    apply hs.table_extend index hindex _ htable delta.val ?_ count hcount hlimit
    simpa [hold] using hlength

/-- A raw memory-growth effect extends the decoded store. -/
theorem MemoryGrowth.extends {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) (shape : Shape view s) (syntaxProof : StoreSyntax code s)
    (index : Usize) (delta : U32) (inside : index.val < s.memories.length)
    (result : U32 × runtime.store.Store M) (effect : MemoryGrowth view code s index delta result) :
    Extend_store (decodeStore view code s) (decodeStore view code result.2) := by
  have fresh := effect.shape view code s shape index delta inside result
  have oldWf := decode_store_wf view code s shape syntaxProof
  rcases effect with ⟨_, decoded, _⟩ |
    ⟨old, buffer, count, issued, bytes, countEq, limit, pages, maximum, _, resultEq⟩
  · rw [decoded]
    exact Spec.extend_store_refl _ oldWf
  · rw [resultEq] at fresh ⊢
    have found := (List.getElem?_eq_some_iff.mp issued).2
    let after := {s with memories := s.memories.set index {old with buf := buffer}, memory_bytes := count}
    have newWf := decode_store_wf view code after fresh syntaxProof
    have lengthEq : (view buffer).length = (view old.buf).length + delta.val * 65536 := by
      simpa only [List.length_append, List.length_replicate, Slice.length] using congrArg List.length bytes
    have oldMemoryWf : wf_meminst (decodeMemory view old) := by
      apply wf_meminst.meminst_case_
      · apply wf_memtype.memtype_case_0
        apply decode_limits_wf
        have bound := (shape.memories old (List.mem_of_getElem? issued)).2.1
        scalar_tac
      · exact decode_bytes_wf _
    have newMemoryWf : wf_meminst (decodeMemory view {old with buf := buffer}) := by
      apply wf_meminst.meminst_case_
      · apply wf_memtype.memtype_case_0
        apply decode_limits_wf
        change (view buffer).length / 65536 ≤ _
        rw [lengthEq]
        scalar_tac
      · exact decode_bytes_wf _
    have extension := decode_memory_extends view old {old with buf := buffer}
      rfl (by simp only [lengthEq]; omega) oldMemoryWf newMemoryWf
    change Extend_store (decodeStore view code s)
      {decodeStore view code s with MEMS := (s.memories.set index {old with buf := buffer}).val.map (decodeMemory view)}
    change wf_store {decodeStore view code s with MEMS :=
      (s.memories.set index {old with buf := buffer}).val.map (decodeMemory view)} at newWf
    simp only [alloc.vec.Vec.set_val_eq, List.map_set] at newWf ⊢
    apply Spec.extend_store_set_mem _ _ _ oldWf newWf
    intro indexBound
    simpa only [decodeStore, found,
      getElem!_pos (s.memories.val.map (decodeMemory view)) index.val
        (by simpa only [List.length_map] using inside), List.getElem_map] using extension

/-- A raw table-growth effect with an owned initializer extends the decoded store. -/
theorem TableGrowth.extends {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) (shape : Shape view s) (syntaxProof : StoreSyntax code s)
    (index : Usize) (delta : U32) (value : U64) (inside : index.val < s.tables.length)
    (reference : ReferenceShape s (s.tables.val[index.val]).ty value)
    (result : U32 × runtime.store.Store M) (effect : TableGrowth s index delta value result) :
    Extend_store (decodeStore view code s) (decodeStore view code result.2) := by
  have fresh := effect.shape view s shape index delta value inside reference result
  have oldWf := decode_store_wf view code s shape syntaxProof
  rcases effect with unchanged |
    ⟨old, elements, count, issued, values, maxSize, countEq, limit, maximum, resultEq⟩
  · rw [unchanged.2]
    exact Spec.extend_store_refl _ oldWf
  · rw [resultEq] at fresh ⊢
    have found := (List.getElem?_eq_some_iff.mp issued).2
    let after := {s with tables := s.tables.set index {old with elements}, table_elements := count}
    have newWf := decode_store_wf view code after fresh syntaxProof
    have lengthEq : elements.length = old.elements.length + delta.val := by
      simpa only [List.length_append, List.length_replicate, alloc.vec.Vec.length] using congrArg List.length values
    have oldTableWf : wf_tableinst (decodeTable old) := by
      apply wf_tableinst.tableinst_case_
      apply wf_tabletype.tabletype_case_0
      exact decode_limits_wf _ _ (shape.tables old (List.mem_of_getElem? issued)).1
    have newTableWf : wf_tableinst (decodeTable {old with elements}) := by
      apply wf_tableinst.tableinst_case_
      apply wf_tabletype.tabletype_case_0
      apply decode_limits_wf
      simpa only [lengthEq] using maxSize
    have extension := decode_table_extends old {old with elements} rfl rfl
      (by simp only [lengthEq]; omega) oldTableWf newTableWf
    change Extend_store (decodeStore view code s)
      {decodeStore view code s with TABLES := (s.tables.set index {old with elements}).val.map decodeTable}
    change wf_store {decodeStore view code s with TABLES :=
      (s.tables.set index {old with elements}).val.map decodeTable} at newWf
    simp only [alloc.vec.Vec.set_val_eq, List.map_set] at newWf ⊢
    apply Spec.extend_store_set_table _ _ _ oldWf newWf
    intro indexBound
    simpa only [decodeStore, found,
      getElem!_pos (s.tables.val.map decodeTable) index.val
        (by simpa only [List.length_map] using inside), List.getElem_map] using extension

theorem MemoryGrowth.metadata {M : Type} {view : M → Slice U8} {code : CodeInterpretation}
    {before : runtime.store.Store M} {index delta out} (effect : MemoryGrowth view code before index delta out) :
    Interp.FrameStoreMetadata before out.2 ∧ out.2.externs = before.externs ∧
      out.2.elems = before.elems ∧ out.2.datas = before.datas := by
  rcases effect with ⟨_,_,same | ⟨old,buffer,lookup,viewEq,same⟩⟩ |
    ⟨old,buffer,count,lookup,bytes,used,limit,capacity,maximum,size,same⟩
  all_goals rw [same]; exact ⟨⟨rfl,rfl,rfl,rfl⟩,rfl,rfl,rfl⟩

theorem TableGrowth.metadata {M : Type} {before : runtime.store.Store M} {index delta value out}
    (effect : TableGrowth before index delta value out) :
    Interp.FrameStoreMetadata before out.2 ∧ out.2.externs = before.externs ∧
      out.2.elems = before.elems ∧ out.2.datas = before.datas := by
  rcases effect with ⟨_,same⟩ | ⟨old,words,count,lookup,values,capacity,used,limit,maximum,same⟩
  all_goals rw [same]; exact ⟨⟨rfl,rfl,rfl,rfl⟩,rfl,rfl,rfl⟩
end Itasca.Runtime.Store

end

/-! ## GrowthLimits -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem MemoryGrowth.limits {M : Type} {view : M → Slice U8} {code : CodeInterpretation}
    {before : runtime.store.Store M} {index delta out} (effect : MemoryGrowth view code before index delta out) :
    out.2.limits = before.limits := by
  rcases effect with ⟨_,_,same | ⟨old,buffer,lookup,viewEq,same⟩⟩ |
    ⟨old,buffer,count,lookup,bytes,used,limit,capacity,maximum,size,same⟩
  all_goals rw [same]

theorem TableGrowth.limits {M : Type} {before : runtime.store.Store M} {index delta value out}
    (effect : TableGrowth before index delta value out) : out.2.limits = before.limits := by
  rcases effect with ⟨_,same⟩ | ⟨old,words,count,lookup,values,capacity,used,limit,maximum,same⟩
  all_goals rw [same]
end Itasca.Runtime.Store

end
