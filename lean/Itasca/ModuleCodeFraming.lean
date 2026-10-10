import Itasca.ModuleCodeEntry
import Itasca.ModuleCodeSemantic

open Aeneas Aeneas.Std

namespace Itasca

@[step]
theorem module.code_entry_extent.spec (data : Slice U8) (pos : Usize) :
    module.code_entry_extent data pos ⦃ r => match r with
      | .Ok (content, finish) => ModuleCode.Extent data pos content finish
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  rw [module.code_entry_extent, hr]
  cases r with
  | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
      obtain ⟨size, content⟩ := pair
      have hs := hp.span
      simp [core.result.Result.Insts.CoreOpsTry.branch]
      step
      obtain ⟨r, hh, hhpost⟩ := WP.spec_imp_exists (module.have_bytes.spec data content n hs.2.2)
      rw [hh]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok u =>
          cases u
          have hb := hhpost.1.mp rfl
          simp
          step
          exact ⟨size, hp, by scalar_tac, by scalar_tac⟩

/-- Both paths read the same declared entry size, so a successful validating
callback ends at the independently checked framing boundary. -/
theorem module.code_entry_extent.frames (data : Slice U8) (pos content finish : Usize)
    (env : module.Env) (index next : Usize) (hbound : CodeEntry.Bounds env)
    (hext : ModuleCode.Extent data pos content finish)
    (hentry : module.validate_code_entry data pos env index = .ok (.Ok next)) : finish = next := by
  obtain ⟨⟨r, v⟩, hr, hp⟩ := WP.spec_imp_exists (module.validate_code_entry_with.pipeline
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_total data pos env index () hbound)
  have he : r = .Ok next := by simpa [module.validate_code_entry, hr] using hentry
  obtain ⟨w⟩ := hp next he
  obtain ⟨size, hs, hn, _⟩ := hext
  obtain ⟨heq, hp⟩ := ModuleCode.decoded_unique hs w.header
  apply UScalar.eq_of_val_eq
  have := w.extent
  rw [← heq, ← hp] at this
  omega

theorem module.code_entry_extent.complete (data : Slice U8) (pos first next : Usize)
    (h : ModuleCode.Extent data pos first next) :
    module.code_entry_extent data pos = .ok (.Ok (first, next)) := by
  obtain ⟨count, hc, hn, hb⟩ := h
  have hs : module.code_entry_extent data pos ⦃ r => r = .Ok (first, next) ⦄ := by
    simp [module.code_entry_extent, reader.read_u32_leb.complete data pos count first hc,
      core.result.Result.Insts.CoreOpsTry.branch]
    step
    rw [module.have_bytes.complete data first n (by scalar_tac)]
    simp only [bind_ok]
    step*
    congr 3
    apply UScalar.eq_of_val_eq
    scalar_tac
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hs
  exact hr

end Itasca
