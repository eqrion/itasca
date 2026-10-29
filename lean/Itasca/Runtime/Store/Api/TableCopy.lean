import Itasca.Runtime.Store.Initialization.BulkTableAt
import Itasca.Runtime.Store.Api.TableCopyDistinct
import Itasca.Runtime.Store.Api.TableInitLists
import Itasca.Runtime.Store.Initialization.BulkPreservation
import Itasca.Runtime.Store.Initialization.SegmentObjectEffects
import Itasca.Runtime.Spec.TableCopy
import Itasca.Runtime.Store.Api.TableInit

/-!
Table copy effects, preservation and decoded snapshot semantics. These retain success and error distinctions used by preparation and instantiation.
-/

/-! ## Table Copy Effect -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
def TableCopyEffect {M : Type} (store : runtime.store.Store M) (address : Usize)
    (table sourceTable : runtime.store.TableInst) (destination source count : U64)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M) : Prop :=
  if destination.val+count.val ≤ table.elements.length ∧ source.val+count.val ≤ sourceTable.elements.length then
    ∃ words, out = (.Ok (),{store with tables := store.tables.set address {table with elements := words}}) ∧
      words.val = table.elements.val.setSlice! destination.val (sourceTable.elements.val.slice source.val (source.val+count.val))
  else out = (.Err (.Trap .TableOutOfBounds),store)

theorem bulk_table_copy {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (operand entry tableId sourceId : U32) (sourceAddress tableAddress : runtime.TableAddr)
    (table : runtime.store.TableInst) (sourceTable : runtime.store.TableInst)
    (destination source count : U64)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some code)
    (descriptor : code.indirect.val[entry.val]? = some (tableId, sourceId))
    (mapped : inst.tables.val[sourceId.val]? = some sourceAddress)
    (resolved : store.tables.val[sourceAddress.index.val]? = some sourceTable)
    (tableMapped : inst.tables.val[tableId.val]? = some tableAddress)
    (target : store.tables.val[tableAddress.index.val]? = some table)
    (destinationSlot : slots.val[base.val+operand.val]? = some destination)
    (sourceSlot : slots.val[base.val+operand.val+1]? = some source)
    (countSlot : slots.val[base.val+operand.val+2]? = some count) :
    runtime.interp.bulk.execute memory store instIndex function base slots (.TableCopy operand entry)
      ⦃ out => TableCopyEffect store tableAddress.index table sourceTable
        (bulkWord destination) (bulkWord source) (bulkWord count) out ⦄ := by
  simp only [runtime.interp.bulk.execute]
  step with Interp.vec_index_given store.instances instIndex inst found as ⟨actual, actualEq⟩
  subst actual
  step with Interp.vec_index_given inst.module.functions function code functionFound as ⟨actual, actualEq⟩
  subst actual
  simp only [lift, bind_ok]
  step with Interp.vec_index_given code.indirect (UScalar.cast .Usize entry) (tableId, sourceId)
    (by simpa using descriptor) as ⟨a, b, aEq, bEq⟩
  subst a b
  have bound := (List.getElem?_eq_some_iff.mp countSlot).1
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
  step with Interp.vec_index_given inst.tables (UScalar.cast .Usize tableId) tableAddress
    (by simpa using tableMapped) as ⟨actual, actualEq⟩
  subst actual
  step with Interp.vec_index_given store.tables tableAddress.index table target as ⟨actual, actualEq⟩
  subst actual
  step with Interp.range_effect (bulkWord destination) (bulkWord count) (alloc.vec.Vec.len table.elements)
    .TableOutOfBounds as ⟨result, rangeEffect⟩
  by_cases fitsTarget : (bulkWord destination).val + (bulkWord count).val ≤ table.elements.length
  · change (if (bulkWord destination).val + (bulkWord count).val ≤ table.elements.length then _ else _) at rangeEffect
    rw [if_pos fitsTarget] at rangeEffect
    obtain ⟨dst, rfl, dstStart, dstEnd⟩ := rangeEffect
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with Interp.vec_index_given inst.tables (UScalar.cast .Usize sourceId) sourceAddress
      (by simpa using mapped) as ⟨actual, actualEq⟩
    subst actual
    step with Interp.vec_index_given store.tables sourceAddress.index sourceTable resolved as ⟨actual, actualEq⟩
    subst actual
    step with Interp.range_effect (bulkWord source) (bulkWord count) (alloc.vec.Vec.len sourceTable.elements)
      .TableOutOfBounds as ⟨result, rangeEffect⟩
    by_cases fitsSource : (bulkWord source).val + (bulkWord count).val ≤ sourceTable.elements.length
    · change (if (bulkWord source).val + (bulkWord count).val ≤ sourceTable.elements.length then _ else _) at rangeEffect
      rw [if_pos fitsSource] at rangeEffect
      obtain ⟨src, rfl, srcStart, srcEnd⟩ := rangeEffect
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      by_cases same : tableAddress.index = sourceAddress.index
      · simp only [same,ite_true]
        have sameTable : table=sourceTable := by
          have h := target
          rw [same,resolved] at h
          exact (Option.some.inj h).symm
        subst sourceTable
        by_cases backward : dst.start > src.start
        · simp only [backward,ite_true,lift,bind_ok]
          have lengthBound : (bulkWord count).val ≤ Usize.max := by have size : table.elements.length ≤ Usize.max := table.elements.property; omega
          have castCount := Interp.cast_usize_exact (bulkWord count) lengthBound
          step with table_copy_backward_same store.tables sourceAddress.index dst.start src.start
            (UScalar.cast .Usize (bulkWord count)) table (by simpa [same] using target)
            (by simpa only [UScalar.lt_equiv] using Nat.le_of_lt backward)
            (by simpa [castCount,srcStart] using fitsSource)
            (by simpa [castCount,dstStart] using fitsTarget) as ⟨tables,words,tablesEq,valuesEq⟩
          simp only [TableCopyEffect,fitsTarget,fitsSource,and_self,↓reduceIte]
          exact ⟨words,by simpa only [same] using congrArg (fun t => (core.result.Result.Ok (),{store with tables := t})) tablesEq,
            by simpa only [srcStart,dstStart,castCount] using valuesEq⟩
        · simp only [backward,ite_false]
          step with table_copy_forward_same store.tables sourceAddress.index dst.start src.start
            (bulkWord count) table (by simpa [same] using target)
            (by
              have notLess : ¬ src.start.val < dst.start.val := by simpa only [UScalar.lt_equiv] using backward
              omega)
            (by simpa [srcStart] using fitsSource) (by simpa [dstStart] using fitsTarget)
            as ⟨tables,words,tablesEq,valuesEq⟩
          simp only [TableCopyEffect,fitsTarget,fitsSource,and_self,↓reduceIte]
          exact ⟨words,by simpa only [same] using congrArg (fun t => (core.result.Result.Ok (),{store with tables := t})) tablesEq,
            by simpa only [srcStart,dstStart] using valuesEq⟩
      · simp only [same,ite_false]
        have different : tableAddress.index.val ≠ sourceAddress.index.val := by intro eq; exact same (UScalar.eq_of_val_eq eq)
        step with table_copy_distinct store.tables (bulkWord count) tableAddress.index sourceAddress.index dst src sourceTable table
          different resolved target (by simpa [srcStart] using fitsSource) (by simpa [dstStart] using fitsTarget)
          as ⟨tables,words,tablesEq,valuesEq⟩
        simp only [TableCopyEffect,fitsTarget,fitsSource,and_self,↓reduceIte]
        refine ⟨words,by rw [tablesEq],?_⟩
        rw [valuesEq,copy_segment_eq_copy_into,Spec.Segment.copy_into_eq_set_slice _ _ _ _ _
          (by simpa [srcStart] using fitsSource) (by simpa [dstStart] using fitsTarget)]
        simp only [srcStart,dstStart]
    · change (if (bulkWord source).val + (bulkWord count).val ≤ sourceTable.elements.length then _ else _) at rangeEffect
      rw [if_neg fitsSource] at rangeEffect
      rw [rangeEffect]
      simp_all [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        TableCopyEffect]
  · change (if (bulkWord destination).val + (bulkWord count).val ≤ table.elements.length then _ else _) at rangeEffect
    rw [if_neg fitsTarget] at rangeEffect
    rw [rangeEffect]
    simp_all [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      TableCopyEffect]

end Itasca.Runtime.Store

end

/-! ## Table Copy Preservation -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Copy has the same payload-preserving effect as initialization from an
immutable snapshot of the source table. This is only a proof view. -/
theorem TableCopyEffect.initialization {M : Type} {store : runtime.store.Store M}
    {index table sourceTable destination source count out}
    (effect : TableCopyEffect store index table sourceTable destination source count out) :
    TableInitializationEffect store index table ⟨sourceTable.ty,sourceTable.elements⟩ destination source count out := by
  unfold TableCopyEffect at effect
  unfold TableInitializationEffect
  split at effect
  · rename_i inside
    obtain ⟨words,rfl,values⟩ := effect
    simp only [inside,and_self,↓reduceIte]
    refine ⟨words,rfl,?_⟩
    rw [values,copy_segment_eq_copy_into,Spec.Segment.copy_into_eq_set_slice _ _ _ _ _ inside.2 inside.1]
  · rename_i outside
    simp only [outside,↓reduceIte]
    exact effect

theorem TableCopyEffect.shape {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {sourceIndex : Usize} {index table sourceTable destination source count out}
    (effect : TableCopyEffect store index table sourceTable destination source count out)
    (shape : Shape view store) (target : store.tables.val[index.val]? = some table)
    (sourceFound : store.tables.val[sourceIndex.val]? = some sourceTable)
    (sameType : sourceTable.ty=table.ty) : Shape view out.2 := by
  apply effect.initialization.shape shape target
  intro word member
  rw [←sameType]
  exact (shape.tables sourceTable (List.mem_of_getElem? sourceFound)).2.2 word member

theorem TableCopyEffect.object_metadata {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {index table sourceTable destination source count out}
    (effect : TableCopyEffect store index table sourceTable destination source count out)
    (target : store.tables.val[index.val]? = some table) : SegmentObjectMetadata view store out.2 :=
  effect.initialization.object_metadata target
end Itasca.Runtime.Store

end

/-! ## Table Copy Semantics -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt

theorem table_copy_decodes {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (targetIndex sourceIndex : U32) (address sourceAddress : runtime.TableAddr)
    (table sourceTable : runtime.store.TableInst) (destination source count : Nat) (words : alloc.vec.Vec U64)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.tables.val[targetIndex.val]? = some address)
    (sourceMapped : inst.tables.val[sourceIndex.val]? = some sourceAddress)
    (target : store.tables.val[address.index.val]? = some table)
    (sourceFound : store.tables.val[sourceAddress.index.val]? = some sourceTable)
    (sameType : sourceTable.ty=table.ty)
    (inside : source+count ≤ sourceTable.elements.length ∧ destination+count ≤ table.elements.length)
    (copied : words.val = table.elements.val.setSlice! destination (sourceTable.elements.val.slice source (source+count))) :
    decodeStore view code {store with tables := store.tables.set address.index {table with elements := words}} =
      Spec.Segment.tableCopy (decodeStore view code store) ambient targetIndex.val sourceIndex.val destination source count := by
  have targetRead : ambient.MODULE.TABLES[targetIndex.val]! = address.index.val := by
    simp [moduleEq,decodeInstance,List.getElem!_eq_getElem?_getD,mapped]
  have sourceRead : ambient.MODULE.TABLES[sourceIndex.val]! = sourceAddress.index.val := by
    simp [moduleEq,decodeInstance,List.getElem!_eq_getElem?_getD,sourceMapped]
  have targetLookup : (decodeStore view code store).TABLES[address.index.val]! = decodeTable table := by
    simp [decodeStore,List.getElem!_eq_getElem?_getD,target]
  have sourceLookup : (decodeStore view code store).TABLES[sourceAddress.index.val]! = decodeTable sourceTable := by
    simp [decodeStore,List.getElem!_eq_getElem?_getD,sourceFound]
  have lengthEq : words.length=table.elements.length := by
    simpa only [alloc.vec.Vec.length,List.length_setSlice!] using congrArg List.length copied
  have refsEq : words.val.map (decodeRef table.ty) =
      (table.elements.val.map (decodeRef table.ty)).setSlice! destination
        ((sourceTable.elements.val.map (decodeRef sourceTable.ty)).slice source (source+count)) := by
    rw [sameType,←Spec.Segment.copy_into_eq_set_slice _ _ _ _ _ (by simpa using inside.1) (by simpa using inside.2)]
    rw [copied,←Spec.Segment.copy_into_eq_set_slice _ _ _ _ _ inside.1 inside.2]
    exact copy_into_map _ _ _ _ _ _ inside.1
  unfold Spec.Segment.tableCopy
  rw [targetRead,sourceRead,targetLookup,sourceLookup]
  unfold decodeStore
  simp only [alloc.vec.Vec.set_val_eq,List.map_set,decodeTable,lengthEq,refsEq,Spec.Segment.withRefs]
  rfl

end Itasca.Runtime.Store

end
