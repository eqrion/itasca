import Exec.Store.Api.TableInitSemantics

namespace Exec.Store
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

end Exec.Store
