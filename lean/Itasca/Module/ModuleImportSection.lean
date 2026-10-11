import Itasca.Module.ModuleImports

open Aeneas Aeneas.Std

namespace Itasca.ModuleSections

/-- Ordered semantic import updates, independent of the section loop. -/
inductive ImportsAdded (initial : module.Env) : List module.Import → module.Env → Prop where
  | nil : ImportsAdded initial [] initial
  | snoc {entries before after entry} : ImportsAdded initial entries before →
      ImportAdded before after entry → ImportsAdded initial (entries ++ [entry]) after

theorem ImportsAdded.imports {env entries result} (h : ImportsAdded env entries result) :
    result.imports.val = env.imports.val ++ entries := by
  induction h with
  | nil => simp
  | snoc _ hadd ih => simpa [ih, List.append_assoc] using hadd.1

end Itasca.ModuleSections

namespace Itasca

open ModuleBinary ModuleSections

@[step]
theorem module.decode_import_section_loop.spec (data : Slice U8) (env : module.Env)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hbound : ModuleEnv.Bounded env start.val) :
    module.decode_import_section_loop data env count start 0#u32 ⦃ r => match r.1 with
      | .Ok next => ∃ entries, entries.length = count.val ∧ ImportsAdded env entries r.2 ∧
          At (Rep ImportEncoding) data start (entries.map ModuleEnv.rawImport) next ∧
          ModuleEnv.Bounded r.2 next.val
      | .Err _ => True ⦄ := by
  unfold module.decode_import_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ ∃ entries, entries.length = s.2.2.val ∧
      ImportsAdded env entries s.1 ∧
      At (Rep ImportEncoding) data start (entries.map ModuleEnv.rawImport) s.2.1 ∧
      ModuleEnv.Bounded s.1 s.2.1.val)
  · rintro ⟨current, pos, i⟩ ⟨hi, entries, hlen, henv, hbytes, hbound⟩
    dsimp only at hi hlen henv hbytes hbound
    unfold module.decode_import_section_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : i.val = count.val := by scalar_tac
      exact ⟨entries, by omega, henv, hbytes, hbound⟩
    · rename_i hmore
      obtain ⟨⟨r, updated⟩, hr, hp⟩ := WP.spec_imp_exists (module.decode_import.spec data pos current hbound)
      simp only [hr, bind_ok]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok next =>
        obtain ⟨entry, hadd, hb, hbound⟩ := hp
        simp [core.result.Result.Insts.CoreOpsTry.branch]
        step
        refine ⟨?_, ⟨entries ++ [entry], ?_, .snoc henv hadd, ?_, hbound⟩, ?_⟩
        · scalar_tac
        · simp only [List.length_append, List.length_singleton]; scalar_tac
        · simpa only [List.map_append, List.map_cons, List.map_nil] using hbytes.snoc hb
        · scalar_tac
  · exact ⟨by simp, [], by simp, .nil,
      ⟨[], .nil, Wasm.BytesAt.nil data start hstart⟩, hbound⟩

@[step]
theorem module.decode_import_section.spec (data : Slice U8) (pos : Usize) (env : module.Env)
    (hbound : ModuleEnv.Bounded env pos.val) :
    module.decode_import_section data pos env ⦃ r => match r.1 with
      | .Ok next => ∃ entries, ImportsAdded env entries r.2 ∧
          At (VecEncoding ImportEncoding) data pos (entries.map ModuleEnv.rawImport) next ∧
          ModuleEnv.Bounded r.2 next.val
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e => simp [module.decode_import_section, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    obtain ⟨count, start⟩ := pair
    have hs := hc.span
    obtain ⟨⟨r, result⟩, hloop, hp⟩ := WP.spec_imp_exists
      (module.decode_import_section_loop.spec data env count start hs.2.2 (hbound.mono (by omega)))
    simp [module.decode_import_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
    rw [hloop]
    cases r with
    | Err e => simp
    | Ok next =>
      obtain ⟨entries, hlen, henv, hb, hbound⟩ := hp
      exact ⟨entries, henv, At.vector hc hb (by simpa using hlen), hbound⟩

end Itasca
