import Itasca.Module.Readers.Utf8

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary

/-- Name parsing preserves the exact bytes and proves strict UTF-8 validity. -/
@[step]
theorem module.decode_name.spec (data : Slice U8) (start : Usize) :
    module.decode_name data start ⦃ r => match r with
      | .Ok (value, next) => At NameEncoding data start value.val next
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data start)
  cases r with
  | Err e =>
      simp [module.decode_name, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
      obtain ⟨len, pos⟩ := pair
      have hspan := hd.span
      simp [module.decode_name, hr, core.result.Result.Insts.CoreOpsTry.branch]
      step*
      cases r1 with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok u =>
          cases u
          have hbound := r1_post.mp rfl
          simp only [bind_ok]
          step*
          cases r2 with
          | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok u =>
              cases u
              simp only [bind_ok, WP.spec_ok]
              have hutf := r2_post rfl
              have hlength : bytes.val.length = len.val := by
                have := bytes_post.length
                scalar_tac
              obtain ⟨countBytes, hs, hl, hb, he⟩ := hd
              refine ⟨countBytes ++ bytes.val, ⟨?_, by simpa [alloc.vec.Vec.deref] using hutf⟩, ?_⟩
              · exact ByteVecEncoding.iff.mpr ⟨countBytes, by simpa [hlength] using he, rfl⟩
              · exact (show Wasm1.BytesAt data start countBytes pos from ⟨hs, hl, hb⟩).append bytes_post

/-- The checked custom-section name fits in the section; payload bytes remain
uninterpreted, and the public metadata identifies their exact interval. -/
@[step]
theorem module.decode_custom_section.spec (data : Slice U8) (start last : Usize) :
    module.decode_custom_section data start last ⦃ r => match r with
      | .Ok custom => ∃ nm, At NameEncoding data start nm custom.payload_start ∧
          custom.payload_start.val ≤ last.val ∧ custom.payload_end = last ∧
          custom.name_len.val = nm.length
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (module.decode_name.spec data start)
  cases r with
  | Err e =>
      simp [module.decode_custom_section, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
      obtain ⟨nm, next⟩ := pair
      simp [module.decode_custom_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
      split
      · simp
      · rename_i hbound
        simp only [WP.spec_ok]
        exact ⟨nm.val, hd, by scalar_tac, trivial, rfl⟩

end Itasca
