import Exec.Store.Initialization.BulkTableLoop
import Exec.Code.Local.Initializer.InitializerMappings

namespace Exec.Store
open Aeneas Aeneas.Std

theorem bulk_zero_add (value : Usize) : (0#usize + value : Result Usize) = .ok value := by
  have spec : (0#usize + value : Result Usize) ⦃ out => out = value ⦄ := by
    step as ⟨out, equal⟩
    scalar_tac
  obtain ⟨out, call, rfl⟩ := WP.spec_imp_exists spec
  exact call

theorem bulk_zero_cast : UScalar.cast .Usize 0#u32 = 0#usize := by scalar_tac

/-- The encoded i32 operand used by a bulk instruction. -/
abbrev bulkWord (word : U64) : U64 := UScalar.cast .U64 (UScalar.cast .U32 word)

def TableInitializationEffect {M : Type} (store : runtime.store.Store M)
    (tableIndex : Usize) (table : runtime.store.TableInst) (segment : runtime.store.ElemInst)
    (destination source count : U64)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M) : Prop :=
  if destination.val + count.val ≤ table.elements.length ∧ source.val + count.val ≤ segment.refs.length then
    ∃ words, out = (.Ok (), {store with tables := store.tables.set tableIndex {table with elements := words}}) ∧
      words.val = copySegment table.elements.val segment.refs.val destination.val source.val count.val
  else out = (.Err (.Trap .TableOutOfBounds), store)

theorem bulk_table_init {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (store : runtime.store.Store M) (instIndex function : Usize) (slots : Slice U64)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (entry element tableId : U32) (address : Usize) (tableAddress : runtime.TableAddr)
    (table : runtime.store.TableInst) (segment : runtime.store.ElemInst)
    (destination source count : U64)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some code)
    (descriptor : code.indirect.val[entry.val]? = some (element, tableId))
    (mapped : inst.elems.val[element.val]? = some address)
    (resolved : store.elems.val[address.val]? = some segment)
    (tableMapped : inst.tables.val[tableId.val]? = some tableAddress)
    (target : store.tables.val[tableAddress.index.val]? = some table)
    (destinationSlot : slots.val[0]? = some destination)
    (sourceSlot : slots.val[1]? = some source)
    (countSlot : slots.val[2]? = some count) :
    runtime.interp.bulk.execute memory store instIndex function 0#usize slots (.TableInit 0#u32 entry)
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
  have read0 := Code.initializer_slice_index slots 0#usize destination destinationSlot
  have read1 := Code.initializer_slice_index slots 1#usize source sourceSlot
  have read2 := Code.initializer_slice_index slots 2#usize count countSlot
  simp only [bulk_zero_cast, bulk_zero_add, bind_ok, read0, read1, read2]
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

end Exec.Store
