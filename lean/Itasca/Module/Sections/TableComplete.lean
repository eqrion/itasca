import Itasca.Module.Sections.Table
import Itasca.Module.Readers.TypesComplete

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary ModuleSections

theorem module.decode_table_section_loop.complete
    (data : Slice U8) (env : module.Env) (profile : ValidationProfile) (count : U32) (pos : Usize) (i : U32)
    (added : List types.TableType) (next : Usize)
    (hb : At (Rep TableTypeEncoding) data pos added next)
    (hc : i.val + added.length = count.val)
    (hv : ∀ ty ∈ added, ModuleBinary.LimitsValid ty.limits limits.MAX_TABLE_ELEMS)
    (hsize : profile = .Wasm1 → env.table_types.val.length + added.length ≤ 1)
    (hallowed : ∀ ty ∈ added, ElemTypeAllowed profile ty.elem)
    (hbound : env.table_types.val.length ≤ pos.val) :
    ∃ result, module.decode_table_section_loop data env profile count pos i = .ok (.Ok next, result) ∧
      TablesAdded env result added := by
  induction added generalizing env pos i with
  | nil =>
    have he := hb.rep_nil
    have hstop : i ≥ count := by simp only [List.length_nil, Nat.add_zero] at hc; scalar_tac
    refine ⟨env, ?_, by exact ⟨by cases env; rfl, by simp⟩⟩
    unfold module.decode_table_section_loop
    rw [loop]
    simp [module.decode_table_section_loop.body, hstop, he]
  | cons ty added ih =>
    obtain ⟨middle, hfirst, hrest⟩ := hb.rep_cons
    have hmore : ¬ i ≥ count := by simp only [List.length_cons] at hc; scalar_tac
    have hread := module.decode_table_type.complete data pos ty middle hfirst (hv ty (by simp)) profile (hallowed ty (by simp))
    have hprogress := hfirst.tableType_progress
    have hnext := hfirst.span.2
    obtain ⟨updatedTypes, hpush, htypes⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec env.table_types ty (by scalar_tac))
    have hlen : updatedTypes.val.length = env.table_types.val.length + 1 := by simp [htypes]
    have hmax : profile = .Wasm1 → updatedTypes.val.length ≤ 1 := by
      intro hprofile
      have hsize := hsize hprofile
      simp only [List.length_cons] at hsize
      omega
    have hcheck := module.check_table_count.complete {env with table_types := updatedTypes} profile hmax
    obtain ⟨j, hj, hjval⟩ := WP.spec_imp_exists
      (U32.add_spec (x := i) (y := 1#u32) (by scalar_tac))
    let updated := {env with table_types := updatedTypes}
    obtain ⟨result, hloop, hadded⟩ := ih updated middle j hrest
      (by simp only [List.length_cons] at hc; scalar_tac)
      (by intro ft hx; exact hv ft (by simp [hx]))
      (by intro hprofile; change updatedTypes.val.length + added.length ≤ 1
          have hsize := hsize hprofile
          simp only [List.length_cons] at hsize; omega)
      (by intro tt hm; exact hallowed tt (by simp [hm]))
      (by change updatedTypes.val.length ≤ middle.val; omega)
    refine ⟨result, ?_, ?_⟩
    · unfold module.decode_table_section_loop at hloop ⊢
      rw [loop]
      simpa [module.decode_table_section_loop.body, hmore, hread,
        hpush, hcheck, hj, core.result.Result.Insts.CoreOpsTry.branch] using hloop
    · refine ⟨?_, ?_⟩
      · rw [hadded.1]
      · simpa [updated, htypes, List.append_assoc] using hadded.2

theorem module.decode_table_section.complete (data : Slice U8) (pos : Usize)
    (env : module.Env) (profile : ValidationProfile) (added : List types.TableType) (next : Usize)
    (hb : At (VecEncoding TableTypeEncoding) data pos added next)
    (hv : ∀ ty ∈ added, ModuleBinary.LimitsValid ty.limits limits.MAX_TABLE_ELEMS)
    (hsize : profile = .Wasm1 → env.table_types.val.length + added.length ≤ 1)
    (hallowed : ∀ ty ∈ added, ElemTypeAllowed profile ty.elem)
    (hbound : env.table_types.val.length ≤ pos.val) :
    ∃ result, module.decode_table_section data pos env profile = .ok (.Ok next, result) ∧
      TablesAdded env result added := by
  obtain ⟨count, middle, hc, hcount, hentries⟩ := hb.vector_split
  obtain ⟨result, hr, hp⟩ := module.decode_table_section_loop.complete
    data env profile count middle 0#u32 added next hentries (by simpa using hc.symm) hv hsize hallowed
    (by have := hcount.span; omega)
  refine ⟨result, ?_, hp⟩
  simp [module.decode_table_section, reader.read_u32_leb.complete data pos count middle hcount,
    core.result.Result.Insts.CoreOpsTry.branch, hr]

end Itasca
