import Exec.Store.Initialization.BulkTableAt
import Exec.Store.Api.TableCopyDistinct
import Exec.Store.Api.TableInitLists
namespace Exec.Store
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
  rw [Code.initializer_slice_index slots position destination (by simpa only [pos] using destinationSlot)]
  simp only [bind_ok,lift]
  step as ⟨position1,position1Eq⟩
  step as ⟨position2,position2Eq⟩
  have pos2 : position2.val = base.val+operand.val+1 := by simpa only [position1Eq,U32.cast_Usize_val_eq] using position2Eq
  rw [Code.initializer_slice_index slots position2 source (by simpa only [pos2] using sourceSlot)]
  simp only [bind_ok,lift]
  step as ⟨position3,position3Eq⟩
  step as ⟨position4,position4Eq⟩
  have pos4 : position4.val = base.val+operand.val+2 := by simpa only [position3Eq,U32.cast_Usize_val_eq] using position4Eq
  rw [Code.initializer_slice_index slots position4 count (by simpa only [pos4] using countSlot)]
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
        rw [valuesEq,copySegment_eq_copyInto,Spec.Segment.copyInto_eq_setSlice _ _ _ _ _
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

end Exec.Store
