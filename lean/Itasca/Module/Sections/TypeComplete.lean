import Itasca.Module.Sections.Type
import Itasca.Module.Readers.TypesComplete

/-!
# Completeness of the type section parser

`module.decode_type_section.profile_complete` (and the Wasm 1.0 `.complete`): an independently
encoded vector of signatures that satisfy the profile restrictions, caps and allowed value types
is accepted, and the environment gains exactly those signatures (`TypesAdded`). The loop versions
carry a count and the signatures remaining. Soundness is in `Module/Sections/Type`.
-/

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary ModuleSections

/-- The type loop accepts the remaining signatures of a repetition span and adds them. -/
theorem module.decode_type_section_loop.profile_complete
    (data : Slice U8) (env : module.Env) (profile : ValidationProfile) (count : U32) (pos : Usize) (i : U32)
    (types : List types.FuncType) (next : Usize)
    (hb : At (Rep FuncTypeEncoding) data pos types next)
    (hc : i.val + types.length = count.val)
    (ht : ∀ ft ∈ types, Profile.FuncType profile ft ∧ Profile.FuncTypeWithinLimits profile ft)
    (hallowed : ∀ ft ∈ types, ∀ ty ∈ ft.params.val ++ ft.results.val, ValueTypeAllowed profile ty)
    (hsize : env.types.val.length ≤ pos.val) :
    ∃ result, module.decode_type_section_loop data env profile count pos i = .ok (.Ok next, result) ∧
      TypesAdded env result types := by
  induction types generalizing env pos i with
  | nil =>
    have he := hb.rep_nil
    have hstop : i ≥ count := by simp only [List.length_nil, Nat.add_zero] at hc; scalar_tac
    refine ⟨env, ?_, by exact ⟨by cases env; rfl, by simp⟩⟩
    unfold module.decode_type_section_loop
    rw [loop]
    simp [module.decode_type_section_loop.body, hstop, he]
  | cons ft types ih =>
    obtain ⟨middle, hfirst, hrest⟩ := hb.rep_cons
    have hprogress := hfirst.funcType_progress
    have hbound := hfirst.span.2
    have hmore : ¬ i ≥ count := by simp only [List.length_cons] at hc; scalar_tac
    have hread := module.decode_func_type.profile_complete data pos ft middle profile hfirst
      (ht ft (by simp)).1 (ht ft (by simp)).2 (hallowed ft (by simp))
    obtain ⟨updatedTypes, hpush, htypes⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec env.types ft (by scalar_tac))
    obtain ⟨j, hj, hjval⟩ := WP.spec_imp_exists
      (U32.add_spec (x := i) (y := 1#u32) (by scalar_tac))
    let updated := {env with types := updatedTypes}
    obtain ⟨result, hloop, hadded⟩ := ih updated middle j hrest
      (by simp only [List.length_cons] at hc; scalar_tac)
      (by intro ft hx; exact ht ft (by simp [hx]))
      (by intro ft hx; exact hallowed ft (by simp [hx]))
      (by simp only [updated, htypes, List.length_append, List.length_singleton]; omega)
    refine ⟨result, ?_, ?_⟩
    · unfold module.decode_type_section_loop
      rw [loop]
      simp [module.decode_type_section_loop.body, hmore, hread,
        hpush, hj, core.result.Result.Insts.CoreOpsTry.branch]
      exact hloop
    · refine ⟨?_, ?_⟩
      · rw [hadded.1]
      · simpa [updated, htypes, List.append_assoc] using hadded.2

/-- `module.decode_type_section` accepts a vector span of admissible signatures and adds them. -/
theorem module.decode_type_section.profile_complete (data : Slice U8) (pos : Usize)
    (env : module.Env) (profile : ValidationProfile) (types : List types.FuncType) (next : Usize)
    (hb : At (VecEncoding FuncTypeEncoding) data pos types next)
    (ht : ∀ ft ∈ types, Profile.FuncType profile ft ∧ Profile.FuncTypeWithinLimits profile ft)
    (hallowed : ∀ ft ∈ types, ∀ ty ∈ ft.params.val ++ ft.results.val, ValueTypeAllowed profile ty)
    (hsize : env.types.val.length ≤ pos.val) :
    ∃ result, module.decode_type_section data pos env profile = .ok (.Ok next, result) ∧
      TypesAdded env result types := by
  obtain ⟨count, middle, hc, hcount, hentries⟩ := hb.vector_split
  obtain ⟨result, hr, hp⟩ := module.decode_type_section_loop.profile_complete
    data env profile count middle 0#u32 types next hentries (by simpa using hc.symm) ht hallowed
    (by have := hcount.span; omega)
  refine ⟨result, ?_, hp⟩
  simp [module.decode_type_section, reader.read_u32_leb.complete data pos count middle hcount,
    core.result.Result.Insts.CoreOpsTry.branch, hr]


/-- Wasm 1.0 form of `module.decode_type_section_loop.profile_complete`. -/
theorem module.decode_type_section_loop.complete
    (data : Slice U8) (env : module.Env) (count : U32) (pos : Usize) (i : U32)
    (types : List types.FuncType) (next : Usize)
    (hb : At (Rep FuncTypeEncoding) data pos types next)
    (hc : i.val + types.length = count.val)
    (ht : ∀ ft ∈ types, ft.results.val.length ≤ 1)
    (hallowed : ∀ ft ∈ types, ∀ ty ∈ ft.params.val ++ ft.results.val, ValueTypeAllowed .Wasm1 ty)
    (hsize : env.types.val.length ≤ pos.val) :
    ∃ result, module.decode_type_section_loop data env .Wasm1 count pos i = .ok (.Ok next, result) ∧
      TypesAdded env result types := by
  exact module.decode_type_section_loop.profile_complete data env .Wasm1 count pos i types next
    hb hc (by simpa [Profile.FuncType, Profile.FuncTypeWithinLimits] using ht) hallowed hsize

/-- Wasm 1.0 form of `module.decode_type_section.profile_complete`. -/
theorem module.decode_type_section.complete (data : Slice U8) (pos : Usize)
    (env : module.Env) (types : List types.FuncType) (next : Usize)
    (hb : At (VecEncoding FuncTypeEncoding) data pos types next)
    (ht : ∀ ft ∈ types, ft.results.val.length ≤ 1)
    (hallowed : ∀ ft ∈ types, ∀ ty ∈ ft.params.val ++ ft.results.val, ValueTypeAllowed .Wasm1 ty)
    (hsize : env.types.val.length ≤ pos.val) :
    ∃ result, module.decode_type_section data pos env .Wasm1 = .ok (.Ok next, result) ∧
      TypesAdded env result types := by
  exact module.decode_type_section.profile_complete data pos env .Wasm1 types next
    hb (by simpa [Profile.FuncType, Profile.FuncTypeWithinLimits] using ht) hallowed hsize

end Itasca
