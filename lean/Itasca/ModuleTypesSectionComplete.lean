import Itasca.ModuleSections
import Itasca.ModuleTypesComplete

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary ModuleSections

theorem module.decode_type_section_loop.complete
    (data : Slice U8) (env : module.Env) (count : U32) (pos : Usize) (i : U32)
    (types : List types.FuncType) (next : Usize)
    (hb : At (Rep FuncTypeEncoding) data pos types next)
    (hc : i.val + types.length = count.val)
    (ht : ∀ ft ∈ types, ft.results.val.length ≤ 1)
    (hsize : env.types.val.length ≤ pos.val) :
    ∃ result, module.decode_type_section_loop data env count pos i = .ok (.Ok next, result) ∧
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
    have hread := module.decode_func_type.complete data pos ft middle hfirst (ht ft (by simp))
    obtain ⟨updatedTypes, hpush, htypes⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec env.types ft (by scalar_tac))
    obtain ⟨j, hj, hjval⟩ := WP.spec_imp_exists
      (U32.add_spec (x := i) (y := 1#u32) (by scalar_tac))
    let updated := {env with types := updatedTypes}
    obtain ⟨result, hloop, hadded⟩ := ih updated middle j hrest
      (by simp only [List.length_cons] at hc; scalar_tac)
      (by intro ft hx; exact ht ft (by simp [hx]))
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

theorem module.decode_type_section.complete (data : Slice U8) (pos : Usize)
    (env : module.Env) (types : List types.FuncType) (next : Usize)
    (hb : At (VecEncoding FuncTypeEncoding) data pos types next)
    (ht : ∀ ft ∈ types, ft.results.val.length ≤ 1)
    (hsize : env.types.val.length ≤ pos.val) :
    ∃ result, module.decode_type_section data pos env = .ok (.Ok next, result) ∧
      TypesAdded env result types := by
  obtain ⟨count, middle, hc, hcount, hentries⟩ := hb.vector_split
  obtain ⟨result, hr, hp⟩ := module.decode_type_section_loop.complete
    data env count middle 0#u32 types next hentries (by simpa using hc.symm) ht
    (by have := hcount.span; omega)
  refine ⟨result, ?_, hp⟩
  simp [module.decode_type_section, reader.read_u32_leb.complete data pos count middle hcount,
    core.result.Result.Insts.CoreOpsTry.branch, hr]

end Itasca
