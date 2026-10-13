import Itasca.Module.Readers.Utf8

/-!
# Name and custom section readers

`module.decode_name.spec`: an accepted name is a length-prefixed byte vector of valid UTF-8.
`module.decode_custom_section.spec`: the name lies within the section and the rest of the payload
is an uninterpreted interval. Completeness is in `Module/Readers/NamesComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary

/-- An accepted name is a `NameEncoding` span and its bytes are returned unchanged. -/
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

/-- The custom section name is a `NameEncoding` span within the section. The returned metadata
gives the name length and the payload interval from the end of the name to `last`. -/
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
