import Itasca.Module.Sections.Memory
import Itasca.Module.Readers.TypesComplete

/-!
# Completeness of the memory section parser

`module.decode_memory_section.complete`: an independently encoded vector of memory types with
limits within `limits.MAX_MEMORY_PAGES`, at most one memory in total, is accepted and the
environment gains those memories (`MemoriesAdded`). Soundness is in `Module/Sections/Memory`.
-/

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary ModuleSections

/-- The memory loop accepts the remaining valid memory types of a repetition span and adds them. -/
theorem module.decode_memory_section_loop.complete
    (data : Slice U8) (env : module.Env) (count : U32) (pos : Usize) (i : U32)
    (added : List types.MemType) (next : Usize)
    (hb : At (Rep MemTypeEncoding) data pos added next)
    (hc : i.val + added.length = count.val)
    (hv : ∀ ty ∈ added, ModuleBinary.LimitsValid ty.limits limits.MAX_MEMORY_PAGES)
    (hsize : env.mem_types.val.length + added.length ≤ 1) :
    ∃ result, module.decode_memory_section_loop data env count pos i = .ok (.Ok next, result) ∧
      MemoriesAdded env result added := by
  induction added generalizing env pos i with
  | nil =>
    have he := hb.rep_nil
    have hstop : i ≥ count := by simp only [List.length_nil, Nat.add_zero] at hc; scalar_tac
    refine ⟨env, ?_, by exact ⟨by cases env; rfl, by simp⟩⟩
    unfold module.decode_memory_section_loop
    rw [loop]
    simp [module.decode_memory_section_loop.body, hstop, he]
  | cons ty added ih =>
    obtain ⟨middle, hfirst, hrest⟩ := hb.rep_cons
    have hmore : ¬ i ≥ count := by simp only [List.length_cons] at hc; scalar_tac
    have hread := module.decode_mem_type.complete data pos ty middle hfirst (hv ty (by simp))
    obtain ⟨updatedTypes, hpush, htypes⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec env.mem_types ty (by simp only [List.length_cons] at hsize; scalar_tac))
    have hlen : updatedTypes.val.length = env.mem_types.val.length + 1 := by simp [htypes]
    have hzero : env.mem_types.val.length = 0 := by simp only [List.length_cons] at hsize; omega
    have hmax : ¬ alloc.vec.Vec.len updatedTypes > limits.MAX_MEMORIES := by
      simp [alloc.vec.Vec.len, limits.MAX_MEMORIES, hlen, hzero]
    obtain ⟨j, hj, hjval⟩ := WP.spec_imp_exists
      (U32.add_spec (x := i) (y := 1#u32) (by scalar_tac))
    let updated := {env with mem_types := updatedTypes}
    obtain ⟨result, hloop, hadded⟩ := ih updated middle j hrest
      (by simp only [List.length_cons] at hc; scalar_tac)
      (by intro ft hx; exact hv ft (by simp [hx]))
      (by change updatedTypes.val.length + added.length ≤ 1; simp only [List.length_cons] at hsize; omega)
    refine ⟨result, ?_, ?_⟩
    · unfold module.decode_memory_section_loop at hloop ⊢
      rw [loop]
      simpa [module.decode_memory_section_loop.body, hmore, hread,
        hpush, hj, core.result.Result.Insts.CoreOpsTry.branch,
        alloc.vec.Vec.len, limits.MAX_MEMORIES, hlen, hzero] using hloop
    · refine ⟨?_, ?_⟩
      · rw [hadded.1]
      · simpa [updated, htypes, List.append_assoc] using hadded.2

/-- `module.decode_memory_section` accepts a vector span of valid memory types and adds them. -/
theorem module.decode_memory_section.complete (data : Slice U8) (pos : Usize)
    (env : module.Env) (added : List types.MemType) (next : Usize)
    (hb : At (VecEncoding MemTypeEncoding) data pos added next)
    (hv : ∀ ty ∈ added, ModuleBinary.LimitsValid ty.limits limits.MAX_MEMORY_PAGES)
    (hsize : env.mem_types.val.length + added.length ≤ 1) :
    ∃ result, module.decode_memory_section data pos env = .ok (.Ok next, result) ∧
      MemoriesAdded env result added := by
  obtain ⟨count, middle, hc, hcount, hentries⟩ := hb.vector_split
  obtain ⟨result, hr, hp⟩ := module.decode_memory_section_loop.complete
    data env count middle 0#u32 added next hentries (by simpa using hc.symm) hv hsize
  refine ⟨result, ?_, hp⟩
  simp [module.decode_memory_section, reader.read_u32_leb.complete data pos count middle hcount,
    core.result.Result.Insts.CoreOpsTry.branch, hr]

end Itasca
