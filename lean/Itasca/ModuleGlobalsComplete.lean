import Itasca.ModuleGlobalSection
import Itasca.ModuleTypesComplete
import Itasca.ModuleConstantsComplete

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

theorem At.global_split {data pos entry next} (h : At GlobalEncoding data pos entry next) :
    ∃ middle, At GlobalTypeEncoding data pos entry.gtype middle ∧
      At ConstEncoding data middle entry.init next := by
  obtain ⟨bytes, ⟨gb, ib, hg, hi, rfl⟩, hs⟩ := h
  obtain ⟨middle, hfirst, hrest⟩ := hs.split
  exact ⟨middle, ⟨_, hg, hfirst⟩, ⟨_, hi, hrest⟩⟩

theorem At.globalType_progress {data pos ty next} (h : At GlobalTypeEncoding data pos ty next) :
    pos.val < next.val := by
  obtain ⟨bytes, rfl, hs⟩ := h
  have := hs.length
  simp only [List.length_cons, List.length_nil] at this
  omega

end Itasca.ModuleBinary

namespace Itasca

open ModuleBinary ModuleSections

theorem module.decode_global_section_loop.complete
    (data : Slice U8) (env : module.Env) (count : U32) (pos : Usize) (i : U32)
    (added : List module.Global) (next : Usize)
    (hb : At (Rep GlobalEncoding) data pos added next)
    (hc : i.val + added.length = count.val)
    (hv : ∀ g ∈ added, ModuleConstants.Valid env g.init g.gtype.valtype)
    (hg : env.globals.val.length ≤ pos.val)
    (ht : env.global_types.val.length ≤ pos.val) :
    ∃ result, module.decode_global_section_loop data env count pos i = .ok (.Ok next, result) ∧
      GlobalsAdded env result added := by
  induction added generalizing env pos i with
  | nil =>
    have he := hb.rep_nil
    have hstop : i ≥ count := by simp only [List.length_nil, Nat.add_zero] at hc; scalar_tac
    refine ⟨env, ?_, by exact ⟨by cases env; rfl, by simp, by simp⟩⟩
    unfold module.decode_global_section_loop
    rw [loop]
    simp [module.decode_global_section_loop.body, hstop, he]
  | cons g added ih =>
    obtain ⟨middle, hfirst, hrest⟩ := hb.rep_cons
    obtain ⟨initStart, htype, hexpr⟩ := hfirst.global_split
    have hprogress := htype.globalType_progress
    have hspan := hexpr.span
    have hmore : ¬ i ≥ count := by simp only [List.length_cons] at hc; scalar_tac
    have hreadtype := module.decode_global_type.complete data pos g.gtype initStart htype
    have hreadexpr := module.decode_const_expr.complete hexpr (hv g (by simp))
    obtain ⟨types, hpush, htypes⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec env.global_types g.gtype (by scalar_tac))
    obtain ⟨globals, hpushglobals, hglobals⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec env.globals g (by scalar_tac))
    obtain ⟨j, hj, hjval⟩ := WP.spec_imp_exists
      (U32.add_spec (x := i) (y := 1#u32) (by scalar_tac))
    let updated := {env with globals := globals, global_types := types}
    obtain ⟨result, hloop, hadded⟩ := ih updated middle j hrest
      (by simp only [List.length_cons] at hc; scalar_tac)
      (by intro g' hx; exact (hv g' (by simp [hx])).append_globals [g.gtype] htypes rfl)
      (by simp only [updated, hglobals, List.length_append, List.length_singleton]; omega)
      (by simp only [updated, htypes, List.length_append, List.length_singleton]; omega)
    refine ⟨result, ?_, ?_⟩
    · unfold module.decode_global_section_loop
      rw [loop]
      simp [module.decode_global_section_loop.body, hmore, hreadtype, hreadexpr,
        hpush, hpushglobals, hj, core.result.Result.Insts.CoreOpsTry.branch]
      exact hloop
    · refine ⟨?_, ?_, ?_⟩
      · rw [hadded.1]
      · simpa [updated, hglobals, List.append_assoc] using hadded.2.1
      · simpa [updated, htypes, List.append_assoc] using hadded.2.2

theorem module.decode_global_section.complete (data : Slice U8) (pos : Usize)
    (env : module.Env) (added : List module.Global) (next : Usize)
    (hb : At (VecEncoding GlobalEncoding) data pos added next)
    (hv : ∀ g ∈ added, ModuleConstants.Valid env g.init g.gtype.valtype)
    (hg : env.globals.val.length ≤ pos.val)
    (ht : env.global_types.val.length ≤ pos.val) :
    ∃ result, module.decode_global_section data pos env = .ok (.Ok next, result) ∧
      GlobalsAdded env result added := by
  obtain ⟨count, middle, hc, hcount, hentries⟩ := hb.vector_split
  obtain ⟨result, hr, hp⟩ := module.decode_global_section_loop.complete
    data env count middle 0#u32 added next hentries (by simpa using hc.symm) hv
    (by have := hcount.span; omega) (by have := hcount.span; omega)
  refine ⟨result, ?_, hp⟩
  simp [module.decode_global_section, reader.read_u32_leb.complete data pos count middle hcount,
    core.result.Result.Insts.CoreOpsTry.branch, hr]

end Itasca
