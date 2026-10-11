import Itasca.Stream.StreamBatchTotal
import Itasca.Profile.EntryComplete
import Itasca.Module.ModuleCodeEntryComplete

open Aeneas Aeneas.Std

namespace Itasca

variable {profile : ValidationProfile}
open ModuleBinary

/-- An accepting worker validates the independently encoded next entry and
advances exactly one function, without requiring prior dispatch. -/
theorem stream.CodeBatch.validate_func.complete {V : Type} (visitor : code.OpVisitor V)
    (haccept : FullVisitor.Accepts visitor) (batch : stream.CodeBatch) (index : Usize)
    (entry : Code) (finish : Usize) (v : V)
    (herror : batch.error = none) (hcount : batch.num_validated.val < batch.num_funcs.val)
    (hindex : index.val = batch.first_func.val + batch.num_validated.val)
    (hi : index.val < batch.env.func_type_indices.val.length)
    (htyped : CodeEntry.Typed batch.env batch.env.func_type_indices.val[index.val] entry profile)
    (henv : Profile.Environment profile batch.env)
    (hlimits : Profile.EnvironmentWithinLimits profile batch.env) (hbound : CodeEntry.Bounds batch.env)
    (hbytes : At (Profile.CodeEncodingWithinLimits profile) batch.code batch.validated_end entry finish)
    (hprofile : batch.profile = profile) :
    ∃ count v', count.val = batch.num_validated.val + 1 ∧
      stream.CodeBatch.validate_func visitor batch index v = .ok (.Ok (),
        { batch with num_validated := count, validated_end := finish }, v') := by
  obtain ⟨v', hentry⟩ := module.validate_code_entry_with.profile_complete visitor haccept
    batch.code batch.validated_end batch.env index entry finish v profile hi htyped henv hlimits hbound hbytes
  obtain ⟨expected, hadd, hexpected⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x := batch.first_func) (y := batch.num_validated) (by scalar_tac))
  have heq : expected = index := by apply UScalar.eq_of_val_eq; omega
  subst expected
  have hn : ¬ batch.num_validated ≥ batch.num_funcs := by scalar_tac
  have hnext : stream.CodeBatch.validate_next visitor batch index v = .ok (.Ok finish, v') := by
    simp [stream.CodeBatch.validate_next, hn, hadd, hprofile, hentry]
  obtain ⟨count, hinc, hcountval⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x := batch.num_validated) (y := 1#usize) (by scalar_tac))
  refine ⟨count, v', by simpa using hcountval, ?_⟩
  simp [stream.CodeBatch.validate_func, herror, core.option.Option.is_none, hnext, hinc]

/-- Repeated actual validation consumes the independently encoded remaining
entries, in order, and reaches the exact declared function and byte boundary. -/
theorem stream.CodeBatch.validate_all_loop.complete (batch : stream.CodeBatch)
    (entries : List Code) (finish : Usize)
    (herror : batch.error = none)
    (hcount : batch.num_validated.val + entries.length = batch.num_funcs.val)
    (htyped : ModuleCode.EntriesTyped (profile := profile) batch.env
      (batch.first_func.val + batch.num_validated.val) entries)
    (henv : Profile.Environment profile batch.env)
    (hlimits : Profile.EnvironmentWithinLimits profile batch.env) (hbound : CodeEntry.Bounds batch.env)
    (hbytes : At (Rep (Profile.CodeEncodingWithinLimits profile)) batch.code batch.validated_end entries finish)
    (hprofile : batch.profile = profile) :
    stream.CodeBatch.validate_all_loop batch true = .ok
      (batch.module_id, batch.batch_id, batch.profile, batch.env, batch.code, batch.code_offset,
        batch.first_func, batch.num_funcs, batch.num_dispatched, batch.dispatch_end,
        batch.num_funcs, finish, none) := by
  induction entries generalizing batch with
  | nil =>
    have hc : batch.num_validated = batch.num_funcs := by
      apply UScalar.eq_of_val_eq
      simpa using hcount
    have hp := hbytes.rep_nil
    rw [stream.CodeBatch.validate_all_loop, loop]
    simp [stream.CodeBatch.validate_all_loop.body, hc, hp, herror]
  | cons entry entries ih =>
    have hc : batch.num_validated.val < batch.num_funcs.val := by
      simp only [List.length_cons] at hcount
      omega
    cases htyped with
    | cons ht hrest =>
      obtain ⟨hi, ht, _⟩ := ht
      obtain ⟨index, hadd, hindex⟩ := WP.spec_imp_exists
        (UScalar.add_spec (x := batch.first_func) (y := batch.num_validated) (by scalar_tac))
      obtain ⟨next, hentry, hremaining⟩ := hbytes.rep_cons
      obtain ⟨count, v', hcountval, hstep⟩ := stream.CodeBatch.validate_func.complete
        code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_accepts
        batch index entry next () herror hc hindex (by simpa [hindex] using hi)
        (by simpa [hindex] using ht) henv hlimits hbound hentry hprofile
      cases v'
      have hrest' : ModuleCode.EntriesTyped (profile := profile) batch.env
          (batch.first_func.val + count.val) entries := by
        convert hrest using 1
        omega
      have hrec := ih { batch with num_validated := count, validated_end := next }
        herror (by simp only [List.length_cons] at hcount; dsimp only; omega)
        hrest' henv hlimits hbound hremaining hprofile
      have hlt : batch.num_validated < batch.num_funcs := by scalar_tac
      rw [stream.CodeBatch.validate_all_loop, loop]
      simpa [stream.CodeBatch.validate_all_loop.body, hlt, hadd, hstep,
        core.result.Result.is_ok, stream.CodeBatch.validate_all_loop] using hrec

/-- Valid batch contents complete by running the real worker loop; the premise
is independent entry encoding and typing, not an assumed successful worker. -/
theorem stream.CodeBatch.validate_all.complete (batch : stream.CodeBatch)
    (entries : List Code) (finish : Usize)
    (herror : batch.error = none)
    (hcount : batch.num_validated.val + entries.length = batch.num_funcs.val)
    (htyped : ModuleCode.EntriesTyped (profile := profile) batch.env
      (batch.first_func.val + batch.num_validated.val) entries)
    (henv : Profile.Environment profile batch.env)
    (hlimits : Profile.EnvironmentWithinLimits profile batch.env) (hbound : CodeEntry.Bounds batch.env)
    (hbytes : At (Rep (Profile.CodeEncodingWithinLimits profile)) batch.code batch.validated_end entries finish)
    (hprofile : batch.profile = profile) :
    stream.CodeBatch.validate_all batch = .ok
      { batch with num_validated := batch.num_funcs, validated_end := finish, error := none } := by
  simp [stream.CodeBatch.validate_all,
    stream.CodeBatch.validate_all_loop.complete batch entries finish herror hcount htyped henv hlimits hbound hbytes hprofile]

/-- A legitimately issued, independently valid batch runs to a reachable state
whose actual finish check succeeds. This discharges an accepting worker policy. -/
theorem stream.CodeBatch.validate_all.complete_seed (issued : StreamBatch.Issued)
    (entries : List Code) (hissued : issued.Bounded)
    (hcount : entries.length = issued.num_funcs.val)
    (htyped : ModuleCode.EntriesTyped (profile := profile) issued.env issued.first_func.val entries)
    (henv : Profile.Environment profile issued.env)
    (hlimits : Profile.EnvironmentWithinLimits profile issued.env) (hbound : CodeEntry.Bounds issued.env)
    (hbytes : Rep (Profile.CodeEncodingWithinLimits profile) entries issued.code.val)
    (hprofile : issued.profile = profile) :
    ∃ after, stream.CodeBatch.validate_all issued.seed = .ok after ∧
      StreamBatch.Reachable issued after ∧ stream.CodeBatch.finish after = .ok (.Ok ()) := by
  have hb : At (Rep (Profile.CodeEncodingWithinLimits profile)) issued.code 0#usize entries
      (Slice.len issued.code) := ⟨issued.code.val, hbytes, by constructor <;> simp⟩
  have hr := stream.CodeBatch.validate_all.complete issued.seed entries (Slice.len issued.code)
    rfl (by simpa [StreamBatch.Issued.seed] using hcount)
    (by simpa [StreamBatch.Issued.seed] using htyped) henv hlimits hbound hb hprofile
  have hs := stream.CodeBatch.validate_all.spec issued issued.seed hissued hbound .seed hprofile
  rw [hr] at hs
  simp only [WP.spec_ok] at hs
  refine ⟨_, hr, hs, ?_⟩
  apply (stream.CodeBatch.finish.accepted_iff _).mpr
  simp [StreamBatch.Issued.seed]

end Itasca
