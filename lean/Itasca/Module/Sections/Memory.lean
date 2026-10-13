import Itasca.Module.Sections.Type

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

theorem At.memType_progress {data start ty next} (h : At MemTypeEncoding data start ty next) :
    start.val < next.val := by
  obtain ⟨bytes, he, hs⟩ := h
  change LimitsEncoding ty.limits bytes at he
  generalize ty.limits = lim at he
  cases he <;> have := hs.length <;> simp only [List.length_cons, List.length_append] at this <;> omega

end Itasca.ModuleBinary

namespace Itasca.ModuleSections

def MemoriesAdded (env result : module.Env) (added : List types.MemType) : Prop :=
  result = { env with mem_types := result.mem_types } ∧ result.mem_types.val = env.mem_types.val ++ added

end Itasca.ModuleSections

namespace Itasca

open ModuleBinary ModuleSections

@[step]
theorem module.decode_memory_section_loop.spec (data : Slice U8) (env : module.Env)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hsize : env.mem_types.val.length ≤ start.val) :
    module.decode_memory_section_loop data env count start 0#u32 ⦃ r => match r.1 with
      | .Ok next => ∃ added, added.length = count.val ∧ MemoriesAdded env r.2 added ∧
          At (Rep MemTypeEncoding) data start added next ∧
          (∀ ft ∈ added, ModuleTranslation.LimitsValid ft.limits (2 ^ 16)) ∧ r.2.mem_types.val.length ≤ next.val ∧
          r.2.mem_types.val.length ≤ max env.mem_types.val.length 1
      | .Err _ => True ⦄ := by
  unfold module.decode_memory_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ ∃ added, added.length = s.2.2.val ∧
      MemoriesAdded env s.1 added ∧ At (Rep MemTypeEncoding) data start added s.2.1 ∧
      (∀ ft ∈ added, ModuleTranslation.LimitsValid ft.limits (2 ^ 16)) ∧ s.1.mem_types.val.length ≤ s.2.1.val ∧
      s.1.mem_types.val.length ≤ max env.mem_types.val.length 1)
  · rintro ⟨current, pos, i⟩ ⟨hi, added, hlen, henv, hbytes, hvalid, hsize, hcount⟩
    dsimp only at hi hlen henv hbytes hvalid hsize hcount
    unfold module.decode_memory_section_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : i.val = count.val := by scalar_tac
      exact ⟨added, by omega, henv, hbytes, hvalid, hsize, hcount⟩
    · rename_i hmore
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (module.decode_mem_type.spec data pos)
      rw [hr]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
        obtain ⟨ft, next⟩ := pair
        obtain ⟨hb, ht⟩ := hp
        have hprogress := hb.memType_progress
        have hbound := hb.span.2
        have hcapacity : current.mem_types.val.length < Usize.max := by scalar_tac
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step
        split
        · simp
        · rename_i hmax
          step
          refine ⟨?_, ⟨added ++ [ft], ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
          · scalar_tac
          · simp only [List.length_append, List.length_singleton]; scalar_tac
          · constructor
            · rw [henv.1]
            · simp [r_post, henv.2, List.append_assoc]
          · exact hbytes.snoc hb
          · intro ty hm
            rcases List.mem_append.mp hm with hm | hm
            · exact hvalid ty hm
            · simpa [List.mem_singleton.mp hm, ModuleTranslation.LimitsValid, ModuleBinary.LimitsValid,
                Option.mem_def, global_simps, U32.rMax] using ht
          · simp only [r_post, List.length_append, List.length_singleton]; omega
          · have hx : r.val.length ≤ 1 := by simpa [global_simps] using hmax
            exact hx.trans (Nat.le_max_right _ _)
          · scalar_tac
  · exact ⟨by simp, [], by simp, ⟨by cases env; rfl, by simp⟩,
      ⟨[], .nil, Wasm.BytesAt.nil data start hstart⟩, by simp, hsize, Nat.le_max_left _ _⟩

@[step]
theorem module.decode_memory_section.spec (data : Slice U8) (pos : Usize) (env : module.Env)
    (hsize : env.mem_types.val.length ≤ pos.val) :
    module.decode_memory_section data pos env ⦃ r => match r.1 with
      | .Ok next => ∃ added, MemoriesAdded env r.2 added ∧
          At (VecEncoding MemTypeEncoding) data pos added next ∧
          (∀ ft ∈ added, ModuleTranslation.LimitsValid ft.limits (2 ^ 16)) ∧ r.2.mem_types.val.length ≤ next.val ∧
          r.2.mem_types.val.length ≤ max env.mem_types.val.length 1
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e => simp [module.decode_memory_section, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    obtain ⟨count, start⟩ := pair
    have hs := hc.span
    obtain ⟨⟨r, result⟩, hloop, hp⟩ := WP.spec_imp_exists
      (module.decode_memory_section_loop.spec data env count start hs.2.2 (by omega))
    simp [module.decode_memory_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
    rw [hloop]
    cases r with
    | Err e => simp
    | Ok next =>
      obtain ⟨added, hlen, henv, hb, ht, hsize, hcount⟩ := hp
      exact ⟨added, henv, At.vector hc hb hlen, ht, hsize, by simpa using hcount⟩

end Itasca
