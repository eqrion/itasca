import Exec.Interp.Relations.Admin

/-! The interpreter copies slots from low to high. The mathematical operation
retains that order, including the behavior of overlapping source/destination
ranges. Branch and return proofs additionally establish downward movement. -/
namespace Exec.Interp
open Aeneas Aeneas.Std

def copyWords (words : List U64) (dst src : Nat) : Nat → List U64
  | 0 => words
  | n + 1 => copyWords (words.set dst words[src]!) (dst + 1) (src + 1) n

theorem copyWords_length (words : List U64) (dst src n : Nat) :
    (copyWords words dst src n).length = words.length := by
  induction n generalizing words dst src with
  | zero => rfl
  | succ n ih => simp only [copyWords, ih, List.length_set]

/-- Downward transfers observe the original source words and preserve every
slot outside the destination interval, including when the ranges overlap. -/
theorem copyWords_downward (words : List U64) (dst src n : Nat)
    (order : dst ≤ src) (source : src + n ≤ words.length) :
    (∀ j, j < n → (copyWords words dst src n)[dst + j]? = words[src + j]?) ∧
    (∀ j, j < dst ∨ dst + n ≤ j → (copyWords words dst src n)[j]? = words[j]?) := by
  induction n generalizing words dst src with
  | zero => simp [copyWords]
  | succ n ih =>
    have hs : src < words.length := by omega
    have hd : dst < words.length := by omega
    have hnext := ih (words.set dst words[src]!) (dst + 1) (src + 1)
      (by omega) (by simp only [List.length_set]; omega)
    simp only [copyWords]
    constructor
    · intro j hj
      cases j with
      | zero =>
        have hset : (words.set dst words[src]!)[dst]? = words[src]? := by simp [hd, hs]
        simpa using (hnext.2 dst (Or.inl (by omega))).trans hset
      | succ j =>
        have hjn : j < n := by omega
        have he : dst + (j + 1) = dst + 1 + j := by omega
        rw [he, hnext.1 j hjn]
        have hne : src + 1 + j ≠ dst := by omega
        have hne' : dst ≠ src + 1 + j := Ne.symm hne
        simp only [List.getElem?_set, hne', if_false]
        congr 1 <;> omega
    · intro j hj
      rw [hnext.2 j (by omega)]
      have hne : j ≠ dst := by omega
      simp [List.getElem?_set, hne]

@[step] theorem copy_loop_effect (words : Slice U64) (dst src n i : Usize)
    (hs : src.val + n.val ≤ words.length)
    (hd : dst.val + n.val ≤ words.length)
    (hi : i.val ≤ n.val) :
    runtime.interp.copy_loop words dst src n i ⦃ out =>
      out.val = copyWords words.val (dst.val + i.val) (src.val + i.val) (n.val - i.val) ⦄ := by
  unfold runtime.interp.copy_loop
  apply loop.spec_decr_nat (fun p => n.val - p.2.val)
    (fun p => p.2.val ≤ n.val ∧ p.1.length = words.length ∧
      copyWords p.1.val (dst.val + p.2.val) (src.val + p.2.val) (n.val - p.2.val) =
        copyWords words.val (dst.val + i.val) (src.val + i.val) (n.val - i.val))
  · rintro ⟨current, j⟩ ⟨hj, hlen, hcopy⟩
    dsimp only at hj hlen hcopy
    unfold runtime.interp.copy_loop.body
    dsimp only
    split
    · rename_i hmore
      have hlt : j.val < n.val := by scalar_tac
      step as ⟨readPos, hreadPos⟩
      step as ⟨value, hvalue⟩
      step as ⟨writePos, hwritePos⟩
      step as ⟨updated, hupdated⟩
      step as ⟨next, hnext⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · scalar_tac
      · simpa [hupdated] using hlen
      · have hremaining : n.val - j.val = (n.val - next.val) + 1 := by omega
        rw [hremaining, copyWords] at hcopy
        simp only [hupdated, Slice.set_val_eq, hwritePos, hnext]
        have hv : value = current.val[src.val + j.val]! := by
          have hb : src.val + j.val < current.val.length := by change src.val + j.val < current.length; omega
          rw [_root_.getElem!_pos current.val _ hb]
          simpa [hreadPos] using hvalue
        simpa [hv, hnext, Nat.add_assoc] using hcopy
      · omega
    · have heq : j.val = n.val := by scalar_tac
      simpa [heq, copyWords] using hcopy
  · exact ⟨hi, rfl, rfl⟩

@[step] theorem copy_effect_words (words : Slice U64) (dst src n : Usize)
    (hs : src.val + n.val ≤ words.length)
    (hd : dst.val + n.val ≤ words.length) :
    runtime.interp.copy words dst src n ⦃ out =>
      out.val = copyWords words.val dst.val src.val n.val ⦄ := by
  simpa [runtime.interp.copy] using copy_loop_effect words dst src n 0#usize hs hd (by simp)

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (platform : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

@[step] theorem copy_n_effect (exec : runtime.interp.Execution)
    (base : Usize) (dst src n : U32)
    (hs : base.val + src.val + n.val ≤ exec.slots.length)
    (hd : base.val + dst.val + n.val ≤ exec.slots.length)
    (hsrc : base.val + src.val ≤ Usize.max)
    (hdst : base.val + dst.val ≤ Usize.max) :
    runtime.interp.admin_copy_n memory platform floats allocator exec base dst src n
      ⦃ out => out.1 = .Ok () ∧ SlotsEffect exec out.2
        (copyWords exec.slots.val (base.val + dst.val) (base.val + src.val) n.val) ⦄ := by
  unfold runtime.interp.admin_copy_n
  simp only [lift, bind_ok, alloc.vec.Vec.deref_mut]
  step* <;> simp_all [SlotsEffect] <;> first | assumption | omega

@[step] theorem copy2_effect (exec : runtime.interp.Execution)
    (base : Usize) (dst src : U32)
    (hs : base.val + src.val + 2 ≤ exec.slots.length)
    (hd : base.val + dst.val + 2 ≤ exec.slots.length) :
    runtime.interp.admin_copy2 memory platform floats allocator exec base dst src
      ⦃ out => out.1 = .Ok () ∧ SlotsEffect exec out.2
        (copyWords exec.slots.val (base.val + dst.val) (base.val + src.val) 2) ⦄ := by
  unfold runtime.interp.admin_copy2
  simp only [lift, bind_ok, alloc.vec.Vec.deref_mut]
  step* <;> simp_all [SlotsEffect] <;> first | assumption | omega

/-- Returning copies the declared result words to the caller's destination and
removes exactly the last concrete frame. -/
def ReturnEffect (before after : runtime.interp.Execution) (base src n : Nat) : Prop :=
  after.slots.val = copyWords before.slots.val base (base + src) n ∧
  after.frames.val = before.frames.val.dropLast ∧
  { after with slots := before.slots, frames := before.frames } = before

@[step] theorem return_effect (exec : runtime.interp.Execution)
    (base : Usize) (src n : U32)
    (hs : base.val + src.val + n.val ≤ exec.slots.length)
    (hsrc : base.val + src.val ≤ Usize.max) :
    runtime.interp.admin_return memory platform floats allocator exec base src n
      ⦃ out => out.1 = .Ok () ∧ ReturnEffect exec out.2 base.val src.val n.val ⦄ := by
  have hd : base.val + n.val ≤ exec.slots.slice.length := by
    change base.val + n.val ≤ exec.slots.length
    omega
  unfold runtime.interp.admin_return
  simp only [lift, bind_ok, alloc.vec.Vec.deref_mut]
  step* <;> simp_all [alloc.vec.Vec.pop, ReturnEffect] <;> first | assumption | omega

end Exec.Interp
