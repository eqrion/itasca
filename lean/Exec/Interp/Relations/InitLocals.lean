import Exec.Interp.Relations.Execute

/-! Function entry clears precisely the non-parameter local words. -/
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

def zeroWords (words : List U64) (start : Nat) : Nat → List U64
  | 0 => words
  | n + 1 => zeroWords (words.set start 0#u64) (start + 1) n

theorem zeroWords_length (words : List U64) (start n : Nat) :
    (zeroWords words start n).length = words.length := by
  induction n generalizing words start with
  | zero => rfl
  | succ n ih => simp only [zeroWords, ih, List.length_set]

theorem zeroWords_effect (words : List U64) (start n : Nat)
    (bound : start + n ≤ words.length) :
    (∀ j, j < n → (zeroWords words start n)[start + j]? = some 0#u64) ∧
    (∀ j, j < start ∨ start + n ≤ j → (zeroWords words start n)[j]? = words[j]?) := by
  induction n generalizing words start with
  | zero => simp [zeroWords]
  | succ n ih =>
    have hs : start < words.length := by omega
    have hnext := ih (words.set start 0#u64) (start + 1)
      (by simp only [List.length_set]; omega)
    simp only [zeroWords]
    constructor
    · intro j hj
      cases j with
      | zero =>
        have hset : (words.set start 0#u64)[start]? = some 0#u64 := by simp [hs]
        simpa using (hnext.2 start (Or.inl (by omega))).trans hset
      | succ j => simpa [Nat.add_assoc, Nat.add_comm 1 j] using hnext.1 j (by omega)
    · intro j hj
      rw [hnext.2 j (by omega)]
      have hne : j ≠ start := by omega
      simp [hne]

@[step] theorem init_locals_effect (exec : runtime.interp.Execution)
    (base : Usize) (locals : U32) (start : Usize)
    (bound : base.val + locals.val ≤ exec.slots.length)
    (range : start.val ≤ base.val + locals.val) :
    runtime.interp.call_loop3 exec base locals start ⦃ out => SlotsEffect exec out
      (zeroWords exec.slots.val start.val (base.val + locals.val - start.val)) ⦄ := by
  unfold runtime.interp.call_loop3
  apply loop.spec_decr_nat (fun p => base.val + locals.val - p.2.val)
    (fun p => p.2.val ≤ base.val + locals.val ∧
      p.1.slots.length = exec.slots.length ∧
      { p.1 with slots := exec.slots } = exec ∧
      zeroWords p.1.slots.val p.2.val (base.val + locals.val - p.2.val) =
        zeroWords exec.slots.val start.val (base.val + locals.val - start.val))
  · rintro ⟨current, index⟩ ⟨hindex, hlen, hrest, hwords⟩
    dsimp only at hindex hlen hrest hwords
    unfold runtime.interp.call_loop3.body
    simp only [lift, bind_ok]
    step as ⟨last, hlast⟩
    split
    · have hlt : index.val < base.val + locals.val := by scalar_tac
      step as ⟨old, back, hold, hback⟩
      step as ⟨next, hnext⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · simp [hback, hlen]
      · simpa using hrest
      · have hn : base.val + locals.val - index.val =
            (base.val + locals.val - next.val) + 1 := by omega
        rw [hn, zeroWords] at hwords
        simpa [hback, hnext] using hwords
      · omega
    · have heq : index.val = base.val + locals.val := by scalar_tac
      exact ⟨by simpa [heq, zeroWords] using hwords, hrest⟩
  · exact ⟨range, rfl, rfl, rfl⟩

end Itasca.Runtime.Interp
