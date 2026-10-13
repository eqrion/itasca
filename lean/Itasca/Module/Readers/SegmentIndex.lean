import Itasca.Module.Readers.BasicComplete

open Aeneas Aeneas.Std

namespace Itasca
open ModuleBinary

/-- The segment prefix decoder accounts for the optional explicit index after
the independently decoded version-specific flag or index word. -/
theorem module.decode_segment_index.profile_spec (data : Slice U8) (pos : Usize)
    (flags : U32) (profile : ValidationProfile) (hpos : pos.val ≤ data.length) :
    module.decode_segment_index data pos flags profile ⦃ r => match r with
      | .Ok (idx, next, explicit) =>
          At (fun pair => SegmentIndexEncoding profile flags pair.1 pair.2)
            data pos (idx, explicit) next
      | .Err _ => True ⦄ := by
  cases profile with
  | Wasm1 =>
      simp only [module.decode_segment_index, WP.spec_ok]
      exact ⟨[], ⟨rfl, rfl, rfl⟩, Wasm1.BytesAt.nil data pos hpos⟩
  | Wasm2 =>
      by_cases hzero : flags = 0#u32
      · subst flags
        simp only [module.decode_segment_index]
        exact ⟨[], Or.inl ⟨rfl, rfl, rfl, rfl⟩, Wasm1.BytesAt.nil data pos hpos⟩
      · by_cases htwo : flags = 2#u32
        · subst flags
          obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
          cases r with
          | Err e =>
              simp [module.decode_segment_index, hr, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                error.Error.Insts.CoreConvertFromOpError.from]
          | Ok pair =>
              obtain ⟨idx, next⟩ := pair
              simp only [module.decode_segment_index, hr, core.result.Result.Insts.CoreOpsTry.branch,
                bind_ok]
              obtain ⟨bytes, he, hs⟩ := At.of_u32 hp
              exact ⟨bytes, Or.inr ⟨rfl, rfl, he⟩, hs⟩
        · have h0 : flags.val ≠ 0 := fun h => hzero (UScalar.eq_of_val_eq h)
          have h2 : flags.val ≠ 2 := fun h => htwo (UScalar.eq_of_val_eq h)
          simp only [module.decode_segment_index]
          split
          · exact (h0 rfl).elim
          · exact (h2 rfl).elim
          · simp

theorem module.decode_segment_index.profile_complete {data : Slice U8} {pos next : Usize}
    {flags idx : U32} {explicit : Bool} {profile : ValidationProfile}
    (h : At (fun pair => SegmentIndexEncoding profile flags pair.1 pair.2)
      data pos (idx, explicit) next) :
    module.decode_segment_index data pos flags profile = .ok (.Ok (idx, next, explicit)) := by
  obtain ⟨bytes, he, hs⟩ := h
  cases profile with
  | Wasm1 =>
      obtain ⟨rfl, rfl, rfl⟩ := he
      rw [hs.empty]
      rfl
  | Wasm2 =>
      rcases he with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, he⟩
      · rw [hs.empty]
        rfl
      · simp [module.decode_segment_index, hs.read_u32 idx he,
          core.result.Result.Insts.CoreOpsTry.branch]

end Itasca
