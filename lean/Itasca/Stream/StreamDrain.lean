import Itasca.Support.Result
import Itasca.Stream.StreamScheduler

open Aeneas Aeneas.Std

namespace Itasca.StreamScheduler

variable {profile : ValidationProfile}

/-- Final draining derives certificates for every originally pending issued
identity, while retaining provenance after every poll. -/
theorem drain_sound {V : Type} (visitor : stream.StreamingVisitor V)
    (Tracks : U64 → List StreamBatch.Issued → V → Prop) (hp : Provenance visitor Tracks profile)
    (id : U64) (history : List StreamBatch.Issued) (v v' : V)
    (pending remaining : alloc.vec.Vec Usize) (hv : Tracks id history v)
    (henv : ∀ issued ∈ history, CodeEntry.Bounds issued.env ∧
      ∀ ft ∈ issued.env.types.val, Profile.FuncType profile ft)
    (hprofiles : ∀ issued ∈ history, issued.profile = profile)
    (h : stream.retire_all_code_batches visitor id v pending = .ok (.Ok (), v', remaining)) :
    Tracks id history v' ∧ remaining.val = [] ∧
      ∀ issued ∈ history, issued.module_id = id → issued.batch_id ∈ pending.val → Completed issued profile := by
  generalize hn : pending.val.length = n
  induction n using Nat.strong_induction_on generalizing v pending with
  | h n ih =>
    unfold stream.retire_all_code_batches stream.retire_all_code_batches_loop at h
    rw [loop] at h
    simp only [stream.retire_all_code_batches_loop.body, alloc.vec.Vec.is_empty, bind_ok] at h
    by_cases hempty : pending.val = []
    · simp [hempty] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hv, hempty, by simp [hempty]⟩
    · have hnonempty : pending.val.isEmpty = false := by simpa using hempty
      simp only [hnonempty, Bool.false_eq_true, ↓reduceIte, Std.bind_assoc] at h
      obtain ⟨⟨r, next, rest⟩, hretire, hrest⟩ := ResultFacts.bind_ok_inv _ _ _ h
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hrest
      | Ok u =>
        cases u
        obtain ⟨hvNext, batchId, hperm, hcomplete⟩ :=
          retire_sound visitor Tracks hp id history v next pending rest hv henv hprofiles hretire
        have hlen := hperm.length_eq
        simp only [List.length_cons] at hlen
        have hlt : rest.val.length < n := by omega
        have hrecursive : stream.retire_all_code_batches visitor id next rest =
            .ok (.Ok (), v', remaining) := by
          simpa [stream.retire_all_code_batches, stream.retire_all_code_batches_loop, stream.retire_all_code_batches_loop.body,
            alloc.vec.Vec.is_empty, core.result.Result.Insts.CoreOpsTry.branch] using hrest
        obtain ⟨hvFinal, hnil, hcompleted⟩ := ih rest.val.length hlt next rest hvNext hrecursive rfl
        refine ⟨hvFinal, hnil, ?_⟩
        intro issued hm hmid hpend
        have hmem := hperm.mem_iff.mpr hpend
        rcases List.mem_cons.mp hmem with hid | hrestmem
        · exact hcomplete issued hm hmid hid
        · exact hcompleted issued hm hmid hrestmem

end Itasca.StreamScheduler
