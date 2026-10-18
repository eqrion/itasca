import Exec.Store.Initialization.BulkTableLoop
namespace Exec.Store
open Aeneas Aeneas.Std

/-- Exact left-to-right table-fill writes. -/
def fillTableWords (before : List U64) (start : Nat) (value : U64) : Nat → List U64
  | 0 => before
  | n+1 => (fillTableWords before start value n).set (start+n) value

theorem fillTableWords_length (before : List U64) (start count : Nat) (value : U64) :
    (fillTableWords before start value count).length = before.length := by
  induction count with
  | zero => rfl
  | succ n ih => simp only [fillTableWords,List.length_set,ih]

/-- The extracted table-fill loop terminates and changes exactly the selected
consecutive words, retaining every other table and all table metadata. -/
theorem table_fill_loop (tables : alloc.vec.Vec runtime.store.Table)
    (value : U64) (tableIndex start finish : Usize) (table : runtime.store.Table)
    (target : tables.val[tableIndex.val]? = some table)
    (ordered : start.val ≤ finish.val) (bounded : finish.val ≤ table.elements.length) :
    runtime.interp.bulk.execute_loop2 tables value tableIndex finish start ⦃ out =>
      ∃ words, out = tables.set tableIndex {table with elements := words} ∧
        words.val = fillTableWords table.elements.val start.val value (finish.val-start.val) ⦄ := by
  have tableBound := (List.getElem?_eq_some_iff.mp target).1
  have tableRead := (List.getElem?_eq_some_iff.mp target).2
  unfold runtime.interp.bulk.execute_loop2
  apply loop.spec_decr_nat (fun state => finish.val-state.2.val)
    (fun state => start.val ≤ state.2.val ∧ state.2.val ≤ finish.val ∧ ∃ words : alloc.vec.Vec U64,
      words.val = fillTableWords table.elements.val start.val value (state.2.val-start.val) ∧
      state.1 = tables.set tableIndex {table with elements := words})
  · rintro ⟨current,index⟩ ⟨lower,upper,words,wordValues,currentEq⟩
    dsimp only at lower upper wordValues currentEq ⊢
    have wordLength : words.length = table.elements.length := by
      simpa only [alloc.vec.Vec.length] using (congrArg List.length wordValues).trans (fillTableWords_length _ _ _ _)
    have currentFound : current.val[tableIndex.val]? = some {table with elements := words} := by
      rw [currentEq]
      simp [alloc.vec.Vec.set_val_eq,tableBound]
    unfold runtime.interp.bulk.execute_loop2.body
    split
    · rename_i more
      have less : index.val < finish.val := by simpa only [UScalar.lt_equiv] using more
      have targetInside : index.val < words.length := by omega
      have currentBound : tableIndex.val < current.length := by rw [currentEq]; simpa using tableBound
      step as ⟨actualTable,tableBack,actualEq,tableBackEq⟩
      have actualSame : actualTable = {table with elements := words} := by
        have h := List.getElem?_eq_getElem currentBound
        rw [currentFound] at h
        exact actualEq.trans (Option.some.inj h).symm
      subst actualTable
      step as ⟨old,wordsBack,oldEq,wordsBackEq⟩
      step as ⟨next,nextEq⟩
      refine ⟨?_,?_,⟨words.set index value,?_,?_⟩,?_⟩
      · omega
      · omega
      · have difference : next.val-start.val = (index.val-start.val)+1 := by omega
        simp only [alloc.vec.Vec.set_val_eq,wordValues,difference,fillTableWords]
        congr 1
        omega
      · simp only [wordsBackEq,tableBackEq,currentEq]
        apply alloc.vec.Vec.ext
        simp [alloc.vec.Vec.set_val_eq,List.set_set]
      · omega
    · rename_i more
      have last : index.val = finish.val := by
        have notMore : ¬ index.val < finish.val := by simpa only [UScalar.lt_equiv] using more
        omega
      simp only [WP.spec_ok]
      exact ⟨words,currentEq,by simpa only [last] using wordValues⟩
  · refine ⟨Nat.le_refl _,ordered,table.elements,by simp [fillTableWords],?_⟩
    have same : {table with elements := table.elements} = table := by cases table; rfl
    rw [same,←tableRead,vec_set_current tables tableIndex tableBound]
end Exec.Store
