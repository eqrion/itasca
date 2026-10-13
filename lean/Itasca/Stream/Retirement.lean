import Itasca.Support.Result
import Itasca.Stream.Source

/-!
# Batch retirement

The loops that retire outstanding code batches: `stream.retire_code_batch` polls one worker through
`StreamingVisitor.poll_code_batch`, checks its module identity, removes its batch ID from the
pending vector by swap-and-pop, and requires `stream.CodeBatch.finish` to succeed.
`stream.retire_code_batch.removes` describes the pending vector after a successful retirement, and
`stream.retire_all_code_batches.spec` shows that draining terminates whenever polls return
(`StreamRetirement.PollTotal`), whatever records the scheduler supplies.
-/

open Aeneas Aeneas.Std

namespace Itasca.StreamRetirement

/-- Polling returns an ordinary result in every visitor state. It may report an error or return
an arbitrary record. Termination of retirement needs no batch provenance, worker correctness or
successful finish. -/
def PollTotal {V : Type} (visitor : stream.StreamingVisitor V) : Prop :=
  ∀ state, ∃ r, visitor.poll_code_batch state = .ok r

/-- The pending search finds the first matching entry or its vector's end. -/
def SearchPost (pending : alloc.vec.Vec Usize) (needle first found : Usize) : Prop :=
  first.val ≤ found.val ∧ found.val ≤ pending.length ∧
  (∀ (j : Nat) (hj : j < pending.length), first.val ≤ j → j < found.val →
    pending.val[j] ≠ needle) ∧
  (∀ h : found.val < pending.length, pending.val[found.val] = needle)

end Itasca.StreamRetirement

namespace Itasca

/-- The pending-ID search loop returns the first position from `first` holding `needle`, or the
end of the vector. -/
@[step]
theorem stream.retire_code_batch_loop.spec (pending : alloc.vec.Vec Usize)
    (needle first : Usize) (hfirst : first.val ≤ pending.length) :
    stream.retire_code_batch_loop pending needle first ⦃ StreamRetirement.SearchPost pending needle first ⦄ := by
  unfold stream.retire_code_batch_loop
  apply loop.spec_decr_nat (fun i => pending.length - i.val)
    (fun i => first.val ≤ i.val ∧ i.val ≤ pending.length ∧
      ∀ (j : Nat) (hj : j < pending.length), first.val ≤ j → j < i.val →
        pending.val[j] ≠ needle)
  · intro i hi
    obtain ⟨hlo, hhi, hprev⟩ := hi
    unfold stream.retire_code_batch_loop.body
    by_cases hin : i.val < pending.length
    · have hin' : i < alloc.vec.Vec.len pending := by scalar_tac
      simp only [hin', ↓reduceIte]
      step
      split
      · rename_i hne
        step
        refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
        intro j hj hstart hjnext
        by_cases hji : j < i.val
        · exact hprev j hj hstart hji
        · have heq : j = i.val := by scalar_tac
          subst j
          scalar_tac
      · simp only [WP.spec_ok]
        refine ⟨hlo, hhi, hprev, ?_⟩
        intro h
        scalar_tac
    · have hout : ¬ i < alloc.vec.Vec.len pending := by scalar_tac
      simp only [hout, ↓reduceIte, WP.spec_ok]
      exact ⟨hlo, hhi, hprev, by omega⟩
  · exact ⟨by omega, hfirst, by omega⟩

theorem stream.retire_code_batch_loop.total (pending : alloc.vec.Vec Usize)
    (needle first : Usize) (hfirst : first.val ≤ pending.length) :
    ∃ found, stream.retire_code_batch_loop pending needle first = .ok found := by
  obtain ⟨found, hr, _⟩ := WP.spec_imp_exists (stream.retire_code_batch_loop.spec pending needle first hfirst)
  exact ⟨found, hr⟩

end Itasca

namespace Itasca.StreamRetirement

/-- Swap with the last ID and pop removes exactly the indexed occurrence,
without requiring the vector to be duplicate-free. -/
theorem swap_pop_perm {α : Type} (xs : List α) (i : Nat) (hi : i < xs.length) :
    (xs[i] :: (xs.set i (xs[xs.length - 1]'(by omega))).dropLast).Perm xs := by
  let last := xs[xs.length - 1]'(by omega)
  let ys := xs.set i last
  have hylen : ys.length = xs.length := by simp [ys]
  have hyne : ys ≠ [] := by intro h; have := congrArg List.length h; simp only [List.length_nil, hylen] at this; omega
  have hlast : ys.getLast hyne = last := by
    rw [List.getLast_eq_getElem]
    simp only [ys, List.length_set, List.getElem_set]
    split <;> rfl
  have hdecomp : ys.dropLast ++ [last] = ys := by
    simpa only [hlast] using List.dropLast_append_getLast hyne
  have hrotate : (last :: ys.dropLast).Perm ys := by
    have h : (last :: ys.dropLast).Perm (ys.dropLast ++ [last]) := by
      simpa only [List.singleton_append] using
        (List.perm_append_comm (l₁ := [last]) (l₂ := ys.dropLast))
    rw [hdecomp] at h
    exact h
  have hperm := hrotate.trans (List.set_perm_cons_eraseIdx hi last)
  exact (List.Perm.cons xs[i] (List.Perm.cons_inv hperm)).trans
    (List.getElem_cons_eraseIdx_perm hi)

/-- Under the driver's distinctness invariant, removal excludes the returned
ID and preserves every other member and distinctness. -/
theorem swap_pop_nodup {α : Type} (xs : List α) (i : Nat) (hi : i < xs.length)
    (hn : xs.Nodup) :
    let ys := (xs.set i (xs[xs.length - 1]'(by omega))).dropLast
    ys.Nodup ∧ xs[i] ∉ ys ∧ ∀ x, x ∈ ys ↔ x ∈ xs ∧ x ≠ xs[i] := by
  dsimp only
  have hp := swap_pop_perm xs i hi
  have hn' := hp.nodup_iff.mpr hn
  rw [List.nodup_cons] at hn'
  refine ⟨hn'.2, hn'.1, ?_⟩
  intro x
  constructor
  · intro hx
    refine ⟨hp.mem_iff.mp (by simp [hx]), ?_⟩
    intro he
    subst x
    exact hn'.1 hx
  · rintro ⟨hx, hne⟩
    have := hp.mem_iff.mpr hx
    simpa [hne] using this

end Itasca.StreamRetirement

namespace Itasca.StreamRetirement

/-- A successful retirement comes from an actual poll that returned a batch of the expected module
whose `stream.CodeBatch.finish` succeeded, and the batch ID was removed from the pending vector. -/
def Retired {V : Type} (visitor : stream.StreamingVisitor V) (moduleId : U64)
    (before : V) (pending : alloc.vec.Vec Usize) :
    (core.result.Result Unit error.Error × V × alloc.vec.Vec Usize) → Prop
  | (.Ok (), after, remaining) => ∃ batch,
      visitor.poll_code_batch before = .ok (.Ok batch, after) ∧
      batch.module_id = moduleId ∧ stream.CodeBatch.finish batch = .ok (.Ok ()) ∧
      (batch.batch_id :: remaining.val).Perm pending.val
  | (.Err _, _, _) => True

private theorem finish_returns (batch : stream.CodeBatch) :
    ∃ r, stream.CodeBatch.finish batch = .ok r := by
  unfold stream.CodeBatch.finish
  cases batch.error <;> simp only
  · split
    · split <;> exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

end Itasca.StreamRetirement

namespace Itasca

/-- `stream.retire_code_batch` satisfies `StreamRetirement.Retired` when the reached poll
returns. -/
@[step]
theorem stream.retire_code_batch.spec {V : Type} (visitor : stream.StreamingVisitor V)
    (moduleId : U64) (state : V) (pending : alloc.vec.Vec Usize)
    (hreturn : ∃ r, visitor.poll_code_batch state = .ok r) :
    stream.retire_code_batch visitor moduleId state pending ⦃
      StreamRetirement.Retired visitor moduleId state pending ⦄ := by
  obtain ⟨⟨r, state'⟩, hpoll⟩ := hreturn
  unfold stream.retire_code_batch
  rw [hpoll]
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      StreamRetirement.Retired]
  | Ok batch =>
    simp [core.result.Result.Insts.CoreOpsTry.branch]
    split
    · rename_i hmodule
      obtain ⟨found, hfind, hf⟩ := WP.spec_imp_exists
        (stream.retire_code_batch_loop.spec pending batch.batch_id 0#usize (by simp))
      rw [hfind]
      simp only [bind_ok]
      split
      · simp [StreamRetirement.Retired]
      · rename_i hfound
        have hlt : found.val < pending.length := by have := hf.2.1; scalar_tac
        have hmatch : pending.val[found.val] = batch.batch_id := hf.2.2.2 hlt
        step
        step
        step
        simp only [alloc.vec.Vec.pop, bind_ok]
        obtain ⟨result, hfinish⟩ := StreamRetirement.finish_returns batch
        rw [hfinish]
        simp only [bind_ok]
        cases result with
        | Err e => simp [StreamRetirement.Retired]
        | Ok u =>
          cases u
          refine ⟨batch, hpoll, by scalar_tac, hfinish, ?_⟩
          have hlast : last.val = pending.val.length - 1 := by scalar_tac
          simpa only [index_mut_back_post, i3_post, hlast, alloc.vec.Vec.set_val_eq,
            alloc.vec.Vec.from_val, hmatch] using
            (StreamRetirement.swap_pop_perm pending.val found.val hlt)
    · simp [StreamRetirement.Retired]

end Itasca

namespace Itasca

theorem stream.retire_code_batch.total {V : Type} (visitor : stream.StreamingVisitor V)
    (moduleId : U64) (state : V) (pending : alloc.vec.Vec Usize)
    (hreturn : ∃ r, visitor.poll_code_batch state = .ok r) :
    ∃ r, stream.retire_code_batch visitor moduleId state pending = .ok r := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists
    (stream.retire_code_batch.spec visitor moduleId state pending hreturn)
  exact ⟨r, hr⟩


/-- Successful retirement exposes its actual poll and finish checks without
assuming that any callback returns on unexecuted paths. -/
theorem stream.retire_code_batch.accepted {V : Type} (visitor : stream.StreamingVisitor V)
    (moduleId : U64) (state state' : V) (pending remaining : alloc.vec.Vec Usize)
    (h : stream.retire_code_batch visitor moduleId state pending = .ok (.Ok (), state', remaining)) :
    ∃ batch, visitor.poll_code_batch state = .ok (.Ok batch, state') ∧
      batch.module_id = moduleId ∧ stream.CodeBatch.finish batch = .ok (.Ok ()) ∧
      (batch.batch_id :: remaining.val).Perm pending.val := by
  have hex : ∃ r, visitor.poll_code_batch state = .ok r := by
    unfold stream.retire_code_batch at h
    obtain ⟨r, hr, _⟩ := ResultFacts.bind_ok_inv _ _ _ h
    exact ⟨r, hr⟩
  have hs := stream.retire_code_batch.spec visitor moduleId state pending hex
  simpa [h, StreamRetirement.Retired] using hs

/-- The polled batch ID was pending, is absent from the remaining IDs, and every other pending ID
remains. The driver removes the ID before checking finish. This statement concerns successful
retirements only. -/
theorem stream.retire_code_batch.removes {V : Type} (visitor : stream.StreamingVisitor V)
    (moduleId : U64) (state state' : V) (pending remaining : alloc.vec.Vec Usize)
    (hn : pending.val.Nodup)
    (h : stream.retire_code_batch visitor moduleId state pending = .ok (.Ok (), state', remaining)) :
    ∃ batch, visitor.poll_code_batch state = .ok (.Ok batch, state') ∧
      batch.batch_id ∈ pending.val ∧ batch.batch_id ∉ remaining.val ∧
      remaining.val.Nodup ∧ remaining.length + 1 = pending.length ∧
      (∀ id, id ∈ remaining.val ↔ id ∈ pending.val ∧ id ≠ batch.batch_id) := by
  obtain ⟨batch, hpoll, _, _, hp⟩ := stream.retire_code_batch.accepted
    visitor moduleId state state' pending remaining h
  have hnd := hp.nodup_iff.mpr hn
  rw [List.nodup_cons] at hnd
  refine ⟨batch, hpoll, hp.mem_iff.mp (by simp), hnd.1, hnd.2, ?_, ?_⟩
  · simpa [alloc.vec.Vec.length] using hp.length_eq
  · intro id
    constructor
    · intro hm
      refine ⟨hp.mem_iff.mp (by simp [hm]), ?_⟩
      intro heq
      subst id
      exact hnd.1 hm
    · rintro ⟨hm, hne⟩
      have := hp.mem_iff.mpr hm
      simpa [hne] using this

/-- Draining terminates under returning polls even when those polls supply foreign, unfinished or
fabricated records. An accepted drain leaves the pending vector empty. -/
@[step]
theorem stream.retire_all_code_batches.spec {V : Type} (visitor : stream.StreamingVisitor V)
    (moduleId : U64) (state : V) (pending : alloc.vec.Vec Usize)
    (htotal : StreamRetirement.PollTotal visitor) :
    stream.retire_all_code_batches visitor moduleId state pending ⦃ fun (r, _, remaining) =>
      r = .Ok () → remaining.val = [] ⦄ := by
  unfold stream.retire_all_code_batches stream.retire_all_code_batches_loop
  apply loop.spec_decr_nat (fun s => s.2.length) (fun _ => True)
  · rintro ⟨state, pending⟩ _
    simp only [stream.retire_all_code_batches_loop.body, alloc.vec.Vec.is_empty, bind_ok]
    by_cases hempty : pending.val = []
    · simp [hempty]
    · have hnonempty : pending.val.isEmpty = false := by simpa using hempty
      simp only [hnonempty, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨⟨r, state', remaining⟩, hr, hp⟩ := WP.spec_imp_exists
        (stream.retire_code_batch.spec visitor moduleId state pending (htotal state))
      rw [hr]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok u =>
        cases u
        simp [core.result.Result.Insts.CoreOpsTry.branch]
        obtain ⟨batch, _, _, _, hperm⟩ := hp
        have hlen := hperm.length_eq
        simp only [List.length_cons] at hlen
        change remaining.val.length < pending.val.length
        omega
  · trivial

theorem stream.retire_all_code_batches.total {V : Type} (visitor : stream.StreamingVisitor V)
    (moduleId : U64) (state : V) (pending : alloc.vec.Vec Usize)
    (htotal : StreamRetirement.PollTotal visitor) :
    ∃ r, stream.retire_all_code_batches visitor moduleId state pending = .ok r := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists
    (stream.retire_all_code_batches.spec visitor moduleId state pending htotal)
  exact ⟨r, hr⟩

end Itasca
