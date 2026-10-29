import Itasca.Runtime.Store.Api.TableFillLoop
import Itasca.Runtime.Store.Initialization.BulkTable
import Itasca.Runtime.Spec.TableFill
import Itasca.Runtime.Interp.State.TableMutation
import Itasca.Runtime.Store.Api.TableInit

/-!
Table fill from consecutive word writes to its decoded source effect.

`TableFillEffect` records the checked interval and unchanged-state trap. Its
mutation and decoding lemmas supply table-fill execution and common mutation
facts. The independently consumed word loop remains in `TableFillLoop`.
-/

/-! ## Table Fill Effect -/

section

namespace Itasca.Runtime.Store
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
end Itasca.Runtime.Store

end

/-! ## Table Fill Lists -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem fill_table_words_front (before : List U64) (start count : Nat) (value : U64) :
    fillTableWords before start value (count+1) =
      fillTableWords (before.set start value) (start+1) value count := by
  induction count with
  | zero => simp [fillTableWords]
  | succ count ih =>
    rw [fillTableWords,ih,fillTableWords]
    simp only [Nat.add_assoc,Nat.add_comm 1 count]

theorem fill_table_words_eq (before : List U64) (start count : Nat) (value : U64) :
    fillTableWords before start value count = Spec.Segment.fillInto before start value count := by
  induction count generalizing before start with
  | zero => rfl
  | succ count ih => rw [fill_table_words_front,Spec.Segment.fillInto,ih]
end Itasca.Runtime.Store

end

/-! ## Table Fill Mutation -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca.Runtime.Interp

theorem fill_table_words_member (before : List U64) (start count : Nat) (value word : U64)
    (member : word ∈ fillTableWords before start value count) : word ∈ before ∨ word = value := by
  induction count with
  | zero => exact Or.inl member
  | succ count ih =>
    simp only [fillTableWords] at member
    rcases List.mem_or_eq_of_mem_set member with old | equal
    · exact ih old
    · exact Or.inr equal

theorem TableFillEffect.mutation {M : Type} (store : runtime.store.Store M)
    (address : runtime.TableAddr) (table : runtime.store.TableInst) (destination value count : U64)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M)
    (effect : TableFillEffect store address.index table destination value count out) :
    FrameStoreMetadata store out.2 ∧
    ((out.1 = .Ok () ∧ TableMutation store out.2 address table value) ∨
      (out.1 = .Err (.Trap .TableOutOfBounds) ∧ out.2 = store)) := by
  unfold TableFillEffect at effect
  split at effect
  · obtain ⟨words,rfl,filled⟩ := effect
    refine ⟨⟨rfl,rfl,rfl,rfl⟩,Or.inl ⟨rfl,words,rfl,?_,?_⟩⟩
    · simpa only [alloc.vec.Vec.length] using (congrArg List.length filled).trans (fill_table_words_length _ _ _ _)
    · intro word member
      rw [filled] at member
      exact fill_table_words_member _ _ _ _ _ member
  · rw [effect]
    exact ⟨⟨rfl,rfl,rfl,rfl⟩,Or.inr ⟨rfl,rfl⟩⟩
end Itasca.Runtime.Store

end

/-! ## Table Fill Semantics -/

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

theorem table_fill_decodes {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (tableIndex : U32) (address : runtime.TableAddr) (table : runtime.store.TableInst)
    (destination count : Nat) (value : U64) (words : alloc.vec.Vec U64)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.tables.val[tableIndex.val]? = some address)
    (target : store.tables.val[address.index.val]? = some table)
    (filled : words.val = fillTableWords table.elements.val destination value count) :
    decodeStore view code {store with tables := store.tables.set address.index {table with elements := words}} =
      Spec.Segment.tableFill (decodeStore view code store) ambient tableIndex.val destination (decodeRef table.ty value) count := by
  have tableRead : ambient.MODULE.TABLES[tableIndex.val]! = address.index.val := by
    simp [moduleEq,decodeInstance,List.getElem!_eq_getElem?_getD,mapped]
  have lengthEq : words.length = table.elements.length := by
    simpa only [alloc.vec.Vec.length] using (congrArg List.length filled).trans (fill_table_words_length _ _ _ _)
  have refsEq : words.val.map (decodeRef table.ty) =
      Spec.Segment.fillInto (table.elements.val.map (decodeRef table.ty)) destination (decodeRef table.ty value) count := by
    rw [filled,fill_table_words_eq,Spec.Segment.fill_into_map]
  have lists := fill_map_set_modify decodeTable
    (fun t => {t with REFS := Spec.Segment.fillInto t.REFS destination (decodeRef table.ty value) count})
    store.tables.val address.index.val table {table with elements := words} target
    (by simp only [decodeTable,lengthEq,refsEq])
  rw [Spec.Segment.table_fill_eq,tableRead]
  unfold decodeStore
  simp only [alloc.vec.Vec.set_val_eq,lists]
  rfl

end Itasca.Runtime.Store

end
