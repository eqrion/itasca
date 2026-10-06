import Itasca.ModuleTraceDefs
import Itasca.ModuleCodeVisitor

open Aeneas Aeneas.Std

namespace Itasca

/-- The absent-code path either reaches EOF or observes a complete non-code
section header. It cannot hide a malformed or truncated lookahead header. -/
theorem module.code_section.absent_at (data : Slice U8) (pos : Usize) (env : module.Env)
    (hpos : pos.val ≤ data.length)
    (h : module.code_section data pos env = .ok (.Ok none)) :
    ModuleCode.AbsentAt data pos := by
  unfold module.code_section at h
  by_cases hp : pos ≥ Slice.len data
  · exact Or.inl (by scalar_tac)
  rw [if_neg hp] at h
  obtain ⟨r, hr, hs⟩ := WP.spec_imp_exists (module.read_section_header.spec data pos)
  rw [hr] at h
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
  | Ok tuple =>
    obtain ⟨id, first, last⟩ := tuple
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch] at h
    by_cases hid : id = 10#u8
    · subst id
      simp [module.SECTION_CODE] at h
      obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data first)
      rw [hr] at h
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          error.Error.Insts.CoreConvertFromOpError.from] at h
      | Ok pair =>
        obtain ⟨count, next⟩ := pair
        simp only [bind_ok] at h
        obtain ⟨n, _, h⟩ := VisitorErasure.bind_ok_inv _ _ _ h
        split at h <;> simp at h
    · exact Or.inr ⟨id, first, last, hs, hid⟩

namespace ModuleTrace

private theorem add_value {x y z : Usize} (h : (x + y : Result Usize) = .ok z) :
    z.val = x.val + y.val := by
  have hs := UScalar.add_equiv x y
  rw [h] at hs
  exact hs.2.1

private theorem header_value {size : Usize} (h : limits.MAX_CODE_HEADER_BYTES = .ok size) :
    size.val = 11 := by
  have hs : limits.MAX_CODE_HEADER_BYTES ⦃ n => n.val = 11 ⦄ := by
    unfold limits.MAX_CODE_HEADER_BYTES limits.MAX_LEB_BYTES
    step*
  simpa only [h, WP.spec_ok] using hs

end ModuleTrace

namespace ModuleCodeVisitor

open ModuleTrace

/-- Every accepted framing iteration records both readiness requests before
its entry handoff, with the independently decoded prefix and entry boundary. -/
theorem EntriesRun.trace {V : Type} {visitor : module.CodeVisitor V}
    {data env v pos index v' finish entries}
    (h : EntriesRun visitor data env v pos index v' finish entries)
    (observe : V → List Event) (hrecords : RecordsCode visitor observe)
    (hpos : pos.val ≤ data.length) :
    ∃ events, observe v' = observe v ++ events ∧
      CodeEntriesTrace data env.func_type_indices.val.length index pos finish events := by
  induction h with
  | done v pos index hs => exact ⟨[], by simp, .done _ _ hs hpos⟩
  | @more v v1 v2 v3 v' pos content last index j need finish entries hm hn hw hf hw2 he hj ht ih =>
    have hext := module.code_entry_extent.spec data pos
    rw [hf, WP.spec_ok] at hext
    have hspan := hext.span
    obtain ⟨events, hlog, htrace⟩ := ih hspan.2.2
    have hlog1 := hrecords.need_bytes v need (.Ok ()) v1 hw
    have hlog2 := hrecords.need_bytes v1 last (.Ok ()) v2 hw2
    have hlog3 := hrecords.entry v2 data env index pos content last v3 he
    refine ⟨.needBytes need :: .needBytes last :: .codeEntry index pos content last :: events,
      ?_, .more hm ?_ (ModuleTrace.add_value hn) hext htrace⟩
    · simpa [hlog1, hlog2, hlog3, List.append_assoc] using hlog
    · simpa using ModuleTrace.add_value hj

/-- A successful section walk exposes every readiness and entry callback,
without asserting that a handoff callback validated its entry. -/
theorem SectionRun.trace {V : Type} {visitor : module.CodeVisitor V}
    {data pos env v v' finish entries}
    (h : SectionRun visitor data pos env v v' finish entries)
    (observe : V → List Event) (hrecords : RecordsCode visitor observe)
    (hpos : pos.val ≤ data.length) :
    ∃ events, observe v' = observe v ++ events ∧
      CodeTrace data env.func_type_indices.val.length pos finish events := by
  cases h with
  | @absent v' size need hs hn hw hc =>
    have hfuncs := module.code_section.spec data pos env
    rw [hc, WP.spec_ok] at hfuncs
    change env.func_type_indices.val = [] at hfuncs
    refine ⟨[.needBytes need], hrecords.need_bytes v need (.Ok ()) v' hw,
      .absent (by simp [hfuncs]) (module.code_section.absent_at data pos env hpos hc) ?_⟩
    simpa [ModuleTrace.header_value hs] using ModuleTrace.add_value hn
  | @present v1 v' size need cs entries hs hn hw hc ht =>
    have hsection := module.code_section.spec data pos env
    rw [hc, WP.spec_ok] at hsection
    obtain ⟨first, hh, hcount, heq⟩ := hsection
    obtain ⟨events, hlog, htrace⟩ := ht.trace observe hrecords hcount.span.2.2
    have hhead := hrecords.need_bytes v need (.Ok ()) v1 hw
    refine ⟨.needBytes need :: events, ?_, .present ?_ hh hcount heq htrace⟩
    · simpa [hhead, List.append_assoc] using hlog
    · simpa [ModuleTrace.header_value hs] using ModuleTrace.add_value hn

end ModuleCodeVisitor

/-- Accepted code callbacks exactly follow independently decoded entry frames.
No callback-totality or callback-validation contract is needed. -/
theorem module.validate_code_with.accepted_trace {V : Type}
    (visitor : module.CodeVisitor V) (observe : V → List ModuleTrace.Event)
    (hrecords : ModuleTrace.RecordsCode visitor observe)
    (data : Slice U8) (pos : Usize) (env : module.Env) (v v' : V) (finish : Usize)
    (hpos : pos.val ≤ data.length)
    (h : module.validate_code_with visitor data pos env v = .ok (.Ok finish, v')) :
    ∃ events, observe v' = observe v ++ events ∧
      ModuleTrace.CodeTrace data env.func_type_indices.val.length pos finish events := by
  obtain ⟨entries, hr⟩ := ModuleCodeVisitor.SectionRun.of_accepted visitor data pos env v v' finish h
  exact hr.trace observe hrecords hpos

end Itasca
