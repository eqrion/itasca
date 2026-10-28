import Itasca.Runtime.Equations

/-! Shared slice lookup and list transport lemmas for concrete representations. -/
namespace Itasca.Runtime.Representation
open Aeneas Aeneas.Std

theorem slice_index_given {T : Type} (values : Slice T) (index : Usize) (value : T)
    (found : values.val[index.val]? = some value) :
    Slice.index_usize values index ⦃ out => out = value ⦄ := by
  have bound : index.val < values.length := (List.getElem?_eq_some_iff.mp found).1
  step as ⟨out, hout⟩
  have read := List.getElem?_eq_getElem bound
  rw [found] at read
  exact hout.trans (Option.some.inj read).symm

theorem lookup_prefix {T : Type} (before after : List T)
    (retained : after.take before.length = before) {index : Nat} {value : T}
    (found : before[index]? = some value) : after[index]? = some value := by
  have bound := (List.getElem?_eq_some_iff.mp found).1
  have same := congrArg (fun values => values[index]?) retained
  have eq : after[index]? = before[index]? := by simpa [List.getElem?_take, bound] using same
  exact eq.trans found

theorem map_set_modify {T U : Type} (decode : T → U) (change : U → U)
    (values : List T) (index : Nat) (old replacement : T)
    (found : values[index]? = some old) (same : decode replacement = change (decode old)) :
    (values.set index replacement).map decode = (values.map decode).modify index change := by
  induction values generalizing index with
  | nil => simp at found
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst old
      simpa using same
    | succ index =>
      simp only [List.getElem?_cons_succ] at found
      simpa using ih index found

end Itasca.Runtime.Representation

namespace Itasca.Runtime
open Aeneas Aeneas.Std

/-- The shared runtime `clear` helper empties any vector. -/
@[step] theorem runtime_clear {T : Type} (values : alloc.vec.Vec T) :
    runtime.clear values ⦃ out => out.val = [] ⦄ := by
  unfold runtime.clear runtime.clear_loop
  apply loop.spec_decr_nat (fun v => v.val.length) (fun _ => True)
  · intro v _
    simp only [runtime.clear_loop.body, alloc.vec.Vec.is_empty, bind_ok]
    split
    · rename_i empty
      simpa using empty
    · rename_i nonempty
      simp [alloc.vec.Vec.pop]
      have : 0 < v.val.length := List.length_pos_iff.mpr (by simpa using nonempty)
      omega
  · trivial

end Itasca.Runtime
