import Itasca.Module.Sections.Type

/-!
# Function section parser

Soundness of `module.decode_function_section` and its loop. `FunctionsAdded` says the environment
gains the decoded type indices and the signatures they resolve to, in order. The decoded span is
a `VecEncoding IndexEncoding`. Completeness is in `Module/Sections/FunctionComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleSections

/-- `result` is `env` with `indices` appended to the function type indices and the resolved
`signatures` appended to the function types, and nothing else changed. -/
def FunctionsAdded (env result : module.Env) (indices : List U32)
    (signatures : List types.FuncType) : Prop :=
  result = { env with func_type_indices := result.func_type_indices, func_types := result.func_types } ∧
    result.func_type_indices.val = env.func_type_indices.val ++ indices ∧
    result.func_types.val = env.func_types.val ++ signatures ∧
    List.Forall₂ (ModuleEnv.Resolves env.types.val) indices signatures

end Itasca.ModuleSections

namespace Itasca

open ModuleBinary ModuleSections

/-- The function loop adds `count` indices forming a `Rep IndexEncoding` span. -/
@[step]
theorem module.decode_function_section_loop.spec (data : Slice U8) (env : module.Env)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hfuncs : env.func_types.val.length ≤ start.val)
    (hindices : env.func_type_indices.val.length ≤ start.val) :
    module.decode_function_section_loop data env count start 0#u32 ⦃ r => match r.1 with
      | .Ok next => ∃ indices signatures, indices.length = count.val ∧
          FunctionsAdded env r.2 indices signatures ∧
          At (Rep IndexEncoding) data start indices next ∧
          r.2.func_types.val.length ≤ next.val ∧ r.2.func_type_indices.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  unfold module.decode_function_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ ∃ indices signatures,
      indices.length = s.2.2.val ∧ FunctionsAdded env s.1 indices signatures ∧
      At (Rep IndexEncoding) data start indices s.2.1 ∧
      s.1.func_types.val.length ≤ s.2.1.val ∧ s.1.func_type_indices.val.length ≤ s.2.1.val)
  · rintro ⟨current, pos, i⟩ ⟨hi, indices, signatures, hlen, henv, hbytes, hfuncs, hindices⟩
    dsimp only at hi hlen henv hbytes hfuncs hindices
    unfold module.decode_function_section_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : i.val = count.val := by scalar_tac
      exact ⟨indices, signatures, by omega, henv, hbytes, hfuncs, hindices⟩
    · rename_i hmore
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
      rw [hr]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          error.Error.Insts.CoreConvertFromOpError.from]
      | Ok pair =>
        obtain ⟨idx, next⟩ := pair
        have hs := hp.span
        obtain ⟨r, ht, hlookup⟩ := WP.spec_imp_exists (module.lookup_type.spec current idx)
        cases r with
        | Err e => simp [ht, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok ft =>
          have hcapacity : current.func_types.val.length < Usize.max := by scalar_tac
          have hcapacity' : current.func_type_indices.val.length < Usize.max := by scalar_tac
          have htypes : current.types = env.types := by rw [henv.1]
          have hresolve : ModuleEnv.Resolves env.types.val idx ft := by
            simpa [ModuleEnv.Resolves, htypes] using hlookup
          simp [ht, core.result.Result.Insts.CoreOpsTry.branch]
          step
          step
          step
          refine ⟨?_, ⟨indices ++ [idx], ?_, ⟨signatures ++ [ft], ?_⟩, ?_, ?_, ?_⟩, ?_⟩
          · scalar_tac
          · simp only [List.length_append, List.length_singleton]; scalar_tac
          · refine ⟨?_, ?_, ?_, ?_⟩
            · rw [henv.1]
            · simp [v1_post, henv.2.1, List.append_assoc]
            · simp [v_post, henv.2.2.1, List.append_assoc]
            · exact List.rel_append henv.2.2.2 (.cons hresolve .nil)
          · exact hbytes.snoc (At.of_u32 hp)
          · simp only [v_post, List.length_append, List.length_singleton]; omega
          · simp only [v1_post, List.length_append, List.length_singleton]; omega
          · scalar_tac
  · exact ⟨by simp, [], [], by simp,
      ⟨by cases env; rfl, by simp, by simp, .nil⟩,
      ⟨[], .nil, Wasm1.BytesAt.nil data start hstart⟩, hfuncs, hindices⟩

/-- `module.decode_function_section` adds the indices of a `VecEncoding IndexEncoding` span with
their resolved signatures. -/
@[step]
theorem module.decode_function_section.spec (data : Slice U8) (pos : Usize) (env : module.Env)
    (hfuncs : env.func_types.val.length ≤ pos.val)
    (hindices : env.func_type_indices.val.length ≤ pos.val) :
    module.decode_function_section data pos env ⦃ r => match r.1 with
      | .Ok next => ∃ indices signatures, FunctionsAdded env r.2 indices signatures ∧
          At (VecEncoding IndexEncoding) data pos indices next ∧
          r.2.func_types.val.length ≤ next.val ∧ r.2.func_type_indices.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e => simp [module.decode_function_section, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    obtain ⟨count, start⟩ := pair
    have hs := hc.span
    obtain ⟨⟨r, result⟩, hloop, hp⟩ := WP.spec_imp_exists
      (module.decode_function_section_loop.spec data env count start hs.2.2 (by omega) (by omega))
    simp [module.decode_function_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
    rw [hloop]
    cases r with
    | Err e => simp
    | Ok next =>
      obtain ⟨indices, signatures, hlen, henv, hb, hf, hi⟩ := hp
      exact ⟨indices, ⟨signatures, henv⟩, At.vector hc hb hlen, hf, hi⟩

end Itasca
