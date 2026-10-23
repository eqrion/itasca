import Exec.Store.Api.TableFillLoop
import Exec.Store.Initialization.BulkTable
namespace Exec.Store
open Aeneas Aeneas.Std

def TableFillEffect {M : Type} (store : runtime.store.Store M) (address : Usize)
    (table : runtime.store.TableInst) (destination value count : U64)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M) : Prop :=
  if destination.val+count.val ≤ table.elements.length then
    ∃ words, out = (.Ok (),{store with tables := store.tables.set address {table with elements := words}}) ∧
      words.val = fillTableWords table.elements.val destination.val value count.val
  else out = (.Err (.Trap .TableOutOfBounds),store)

/-- The actual TABLE_FILL handler performs its bounds check before any write,
then fills the requested interval with the full reference word. -/
theorem bulk_table_fill {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (operand tableId : U32) (inst : runtime.store.ModuleInst) (address : runtime.TableAddr)
    (table : runtime.store.TableInst) (destination value count : U64)
    (found : store.instances.val[instIndex.val]? = some inst)
    (mapped : inst.tables.val[tableId.val]? = some address)
    (target : store.tables.val[address.index.val]? = some table)
    (destinationSlot : slots.val[base.val+operand.val]? = some destination)
    (valueSlot : slots.val[base.val+operand.val+1]? = some value)
    (countSlot : slots.val[base.val+operand.val+2]? = some count) :
    runtime.interp.bulk.execute memory store instIndex function base slots (.TableFill operand tableId) ⦃ out =>
      TableFillEffect store address.index table (bulkWord destination) value (bulkWord count) out ⦄ := by
  have bound := (List.getElem?_eq_some_iff.mp countSlot).1
  simp only [runtime.interp.bulk.execute,lift,bind_ok]
  step as ⟨position,positionEq⟩
  have pos : position.val = base.val+operand.val := by simpa only [U32.cast_Usize_val_eq] using positionEq
  rw [Code.initializer_slice_index slots position destination (by simpa only [pos] using destinationSlot)]
  simp only [bind_ok,lift]
  step as ⟨position1,position1Eq⟩
  step as ⟨position2,position2Eq⟩
  have pos2 : position2.val = base.val+operand.val+1 := by simpa only [position1Eq,U32.cast_Usize_val_eq] using position2Eq
  rw [Code.initializer_slice_index slots position2 value (by simpa only [pos2] using valueSlot)]
  simp only [bind_ok,lift]
  step as ⟨position3,position3Eq⟩
  step as ⟨position4,position4Eq⟩
  have pos4 : position4.val = base.val+operand.val+2 := by simpa only [position3Eq,U32.cast_Usize_val_eq] using position4Eq
  rw [Code.initializer_slice_index slots position4 count (by simpa only [pos4] using countSlot)]
  simp only [bind_ok,lift]
  step with Interp.vec_index_given store.instances instIndex inst found as ⟨actual,actualEq⟩
  subst actual
  step with Interp.vec_index_given inst.tables (UScalar.cast .Usize tableId) address (by simpa only [U32.cast_Usize_val_eq] using mapped) as ⟨actual,actualEq⟩
  subst actual
  step with Interp.vec_index_given store.tables address.index table target as ⟨actual,actualEq⟩
  subst actual
  step with Interp.range_effect (bulkWord destination) (bulkWord count) (alloc.vec.Vec.len table.elements)
    .TableOutOfBounds as ⟨result,rangeEffect⟩
  by_cases fits : (bulkWord destination).val+(bulkWord count).val ≤ table.elements.length
  · change (if (bulkWord destination).val+(bulkWord count).val ≤ table.elements.length then _ else _) at rangeEffect
    rw [if_pos fits] at rangeEffect
    obtain ⟨range,rfl,startEq,endEq⟩ := rangeEffect
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step with table_fill_loop store.tables value address.index range.start range.end table target
      (by omega) (by omega) as ⟨tables,words,tablesEq,wordValues⟩
    simp only [TableFillEffect,fits,↓reduceIte]
    refine ⟨words,by rw [tablesEq],?_⟩
    simpa only [startEq,endEq,Nat.add_sub_cancel_left] using wordValues
  · change (if (bulkWord destination).val+(bulkWord count).val ≤ table.elements.length then _ else _) at rangeEffect
    rw [if_neg fits] at rangeEffect
    rw [rangeEffect]
    simp_all [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,TableFillEffect]
end Exec.Store
