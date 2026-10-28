import Exec.Store.Initialization.BulkTable
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
theorem bulk_table_init_at {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (operand entry element tableId : U32) (address : Usize) (tableAddress : runtime.TableAddr)
    (table : runtime.store.TableInst) (segment : runtime.store.ElemInst)
    (destination source count : U64)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some code)
    (descriptor : code.indirect.val[entry.val]? = some (element, tableId))
    (mapped : inst.elems.val[element.val]? = some address)
    (resolved : store.elems.val[address.val]? = some segment)
    (tableMapped : inst.tables.val[tableId.val]? = some tableAddress)
    (target : store.tables.val[tableAddress.index.val]? = some table)
    (destinationSlot : slots.val[base.val+operand.val]? = some destination)
    (sourceSlot : slots.val[base.val+operand.val+1]? = some source)
    (countSlot : slots.val[base.val+operand.val+2]? = some count) :
    runtime.interp.bulk.execute memory store instIndex function base slots (.TableInit operand entry)
      ⦃ out => TableInitializationEffect store tableAddress.index table segment
        (bulkWord destination) (bulkWord source) (bulkWord count) out ⦄ := by
  simp only [runtime.interp.bulk.execute]
  step with Interp.vec_index_given store.instances instIndex inst found as ⟨actual, actualEq⟩
  subst actual
  step with Interp.vec_index_given inst.module.functions function code functionFound as ⟨actual, actualEq⟩
  subst actual
  simp only [lift, bind_ok]
  step with Interp.vec_index_given code.indirect (UScalar.cast .Usize entry) (element, tableId)
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
    step with Interp.vec_index_given inst.elems (UScalar.cast .Usize element) address
      (by simpa using mapped) as ⟨actual, actualEq⟩
    subst actual
    step with Interp.vec_index_given store.elems address segment resolved as ⟨actual, actualEq⟩
    subst actual
    step with Interp.range_effect (bulkWord source) (bulkWord count) (alloc.vec.Vec.len segment.refs)
      .TableOutOfBounds as ⟨result, rangeEffect⟩
    by_cases fitsSource : (bulkWord source).val + (bulkWord count).val ≤ segment.refs.length
    · change (if (bulkWord source).val + (bulkWord count).val ≤ segment.refs.length then _ else _) at rangeEffect
      rw [if_pos fitsSource] at rangeEffect
      obtain ⟨src, rfl, srcStart, srcEnd⟩ := rangeEffect
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with table_init_loop store.tables store.instances store.elems instIndex element (bulkWord count)
        tableAddress.index dst src inst address segment table found mapped resolved target
        (by simpa only [srcStart] using fitsSource) (by simpa only [dstStart] using fitsTarget)
        as ⟨tables, words, tablesEq, valuesEq⟩
      simp only [TableInitializationEffect, fitsSource, fitsTarget, and_self, ↓reduceIte]
      exact ⟨words, by rw [tablesEq], by simpa only [srcStart, dstStart] using valuesEq⟩
    · change (if (bulkWord source).val + (bulkWord count).val ≤ segment.refs.length then _ else _) at rangeEffect
      rw [if_neg fitsSource] at rangeEffect
      rw [rangeEffect]
      simp_all [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        TableInitializationEffect]
  · change (if (bulkWord destination).val + (bulkWord count).val ≤ table.elements.length then _ else _) at rangeEffect
    rw [if_neg fitsTarget] at rangeEffect
    rw [rangeEffect]
    simp_all [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      TableInitializationEffect]

end Itasca.Runtime.Store
