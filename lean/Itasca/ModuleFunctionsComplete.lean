import Itasca.ModuleFunctions
import Itasca.ModuleReadersComplete

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary ModuleSections

theorem module.lookup_type.complete (env : module.Env) (idx : U32)
    (hi : idx.val < env.types.val.length) :
    module.lookup_type env idx = .ok (.Ok env.types.val[idx.val]) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (module.lookup_type.spec env idx)
  cases r with
  | Err e => have := hp.2; omega
  | Ok ft => obtain ⟨_, rfl⟩ := hp; exact hr

/-- The function section appends each independently decoded type index and the
signature it names, in the same order as the raw declaration vector. -/
theorem module.decode_function_section_loop.complete
    (data : Slice U8) (env : module.Env) (count : U32) (pos : Usize) (i : U32)
    (indices : List U32) (next : Usize)
    (hb : At (Rep IndexEncoding) data pos indices next)
    (hc : i.val + indices.length = count.val)
    (ht : ∀ idx ∈ indices, idx.val < env.types.val.length)
    (hf : env.func_types.val.length ≤ pos.val)
    (hi : env.func_type_indices.val.length ≤ pos.val) :
    ∃ result signatures,
      module.decode_function_section_loop data env count pos i = .ok (.Ok next, result) ∧
      FunctionsAdded env result indices signatures := by
  induction indices generalizing env pos i with
  | nil =>
    have he := hb.rep_nil
    have hstop : i ≥ count := by simp only [List.length_nil, Nat.add_zero] at hc; scalar_tac
    refine ⟨env, [], ?_, ?_⟩
    · unfold module.decode_function_section_loop
      rw [loop]
      simp [module.decode_function_section_loop.body, hstop, he]
    · exact ⟨by cases env; rfl, by simp, by simp, .nil⟩
  | cons idx indices ih =>
    obtain ⟨middle, hidx, hrest⟩ := hb.rep_cons
    have hspan := hidx.index_decoded.span
    have hmore : ¬ i ≥ count := by simp only [List.length_cons] at hc; scalar_tac
    have hidxvalid := ht idx (by simp)
    have hread := hidx.read_index
    have hlookup := module.lookup_type.complete env idx hidxvalid
    obtain ⟨funcs, hpush, hfuncs⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec env.func_types env.types.val[idx.val] (by scalar_tac))
    obtain ⟨ids, hpushids, hids⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec env.func_type_indices idx (by scalar_tac))
    obtain ⟨j, hj, hjval⟩ := WP.spec_imp_exists
      (U32.add_spec (x := i) (y := 1#u32) (by scalar_tac))
    let updated := {env with func_types := funcs, func_type_indices := ids}
    obtain ⟨result, signatures, hloop, hadded⟩ := ih updated middle j hrest
      (by simp only [List.length_cons] at hc; scalar_tac)
      (by intro idx hx; exact ht idx (by simp [hx]))
      (by simp only [updated, hfuncs, List.length_append, List.length_singleton]; omega)
      (by simp only [updated, hids, List.length_append, List.length_singleton]; omega)
    refine ⟨result, env.types.val[idx.val] :: signatures, ?_, ?_⟩
    · unfold module.decode_function_section_loop
      rw [loop]
      simp [module.decode_function_section_loop.body, hmore, hread, hlookup,
        hpush, hpushids, hj, core.result.Result.Insts.CoreOpsTry.branch]
      exact hloop
    · refine ⟨?_, ?_, ?_, .cons ⟨hidxvalid, rfl⟩ hadded.2.2.2⟩
      · rw [hadded.1]
      · simpa [updated, hids, List.append_assoc] using hadded.2.1
      · simpa [updated, hfuncs, List.append_assoc] using hadded.2.2.1

theorem module.decode_function_section.complete (data : Slice U8) (pos : Usize)
    (env : module.Env) (indices : List U32) (next : Usize)
    (hb : At (VecEncoding IndexEncoding) data pos indices next)
    (ht : ∀ idx ∈ indices, idx.val < env.types.val.length)
    (hf : env.func_types.val.length ≤ pos.val)
    (hi : env.func_type_indices.val.length ≤ pos.val) :
    ∃ result signatures,
      module.decode_function_section data pos env = .ok (.Ok next, result) ∧
      FunctionsAdded env result indices signatures := by
  obtain ⟨count, middle, hc, hcount, hentries⟩ := hb.vector_split
  obtain ⟨result, signatures, hr, hp⟩ := module.decode_function_section_loop.complete
    data env count middle 0#u32 indices next hentries (by simpa using hc.symm) ht
    (by have := hcount.span; omega) (by have := hcount.span; omega)
  refine ⟨result, signatures, ?_, hp⟩
  simp [module.decode_function_section, reader.read_u32_leb.complete data pos count middle hcount,
    core.result.Result.Insts.CoreOpsTry.branch, hr]

end Itasca
