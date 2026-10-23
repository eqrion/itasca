import Exec.Store.Api.MemoryInitSemantics

namespace Exec.Store
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

end Exec.Store
