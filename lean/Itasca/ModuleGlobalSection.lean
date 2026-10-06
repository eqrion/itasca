import Itasca.ModuleSections

open Aeneas Aeneas.Std

namespace Itasca.ModuleConstants

theorem Valid.append_globals {env result e t} (h : Valid env e t)
    (suffix : List types.GlobalType)
    (hglobals : result.global_types.val = env.global_types.val ++ suffix)
    (hcount : result.num_imported_globals = env.num_imported_globals) : Valid result e t := by
  cases h with
  | i32 value => exact .i32 value
  | i64 value => exact .i64 value
  | f32 value => exact .f32 value
  | f64 value => exact .f64 value
  | globalGet idx gt hi hgt himport hconst =>
    have hi' : idx.val < result.global_types.val.length := by simp [hglobals]; omega
    exact Valid.globalGet idx gt hi'
      (by simpa only [hglobals, List.getElem_append_left hi] using hgt)
      (by simpa [hcount] using himport) hconst

end Itasca.ModuleConstants

namespace Itasca.ModuleSections

def GlobalsAdded (env result : module.Env) (added : List module.Global) : Prop :=
  result = { env with globals := result.globals, global_types := result.global_types } ∧
  result.globals.val = env.globals.val ++ added ∧
  result.global_types.val = env.global_types.val ++ added.map module.Global.gtype

theorem global_encoded {data start pos next gt init}
    (hg : ModuleBinary.At ModuleBinary.GlobalTypeEncoding data start gt pos)
    (hi : ModuleBinary.At ModuleBinary.ConstEncoding data pos init next) :
    ModuleBinary.At ModuleBinary.GlobalEncoding data start ⟨gt, init⟩ next := by
  obtain ⟨gbytes, hg, hs⟩ := hg
  obtain ⟨ibytes, hi, his⟩ := hi
  exact ⟨gbytes ++ ibytes, ⟨gbytes, ibytes, hg, hi, rfl⟩, hs.append his⟩

end Itasca.ModuleSections

namespace Itasca

open ModuleBinary ModuleSections

@[step]
theorem module.decode_global_section_loop.spec (data : Slice U8) (env : module.Env)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hglobals : env.globals.val.length ≤ start.val)
    (htypes : env.global_types.val.length ≤ start.val) :
    module.decode_global_section_loop data env count start 0#u32 ⦃ r => match r.1 with
      | .Ok next => ∃ added, added.length = count.val ∧ GlobalsAdded env r.2 added ∧
          At (Rep GlobalEncoding) data start added next ∧
          (∀ g ∈ added, ModuleConstants.Valid r.2 g.init g.gtype.valtype) ∧
          r.2.globals.val.length ≤ next.val ∧ r.2.global_types.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  unfold module.decode_global_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ ∃ added, added.length = s.2.2.val ∧
      GlobalsAdded env s.1 added ∧ At (Rep GlobalEncoding) data start added s.2.1 ∧
      (∀ g ∈ added, ModuleConstants.Valid s.1 g.init g.gtype.valtype) ∧
      s.1.globals.val.length ≤ s.2.1.val ∧ s.1.global_types.val.length ≤ s.2.1.val)
  · rintro ⟨current, pos, i⟩ ⟨hi, added, hlen, henv, hbytes, hvalid, hglobals, htypes⟩
    dsimp only at hi hlen henv hbytes hvalid hglobals htypes
    unfold module.decode_global_section_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : i.val = count.val := by scalar_tac
      exact ⟨added, by omega, henv, hbytes, hvalid, hglobals, htypes⟩
    · rename_i hmore
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (module.decode_global_type.spec data pos)
      rw [hr]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
        obtain ⟨gt, middle⟩ := pair
        have hprogress : pos.val < middle.val := by
          obtain ⟨bytes, rfl, hs⟩ := hp
          have := hs.length
          simp only [List.length_cons, List.length_nil] at this
          omega
        obtain ⟨r, hc, hconst⟩ := WP.spec_imp_exists (module.decode_const_expr.spec data middle current gt.valtype)
        cases r with
        | Err e => simp [hc, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok pair =>
          obtain ⟨init, next⟩ := pair
          obtain ⟨hcb, hcv⟩ := hconst
          have hs := hcb.span
          have hcapacity : current.global_types.val.length < Usize.max := by scalar_tac
          have hcapacity' : current.globals.val.length < Usize.max := by scalar_tac
          simp [hc, core.result.Result.Insts.CoreOpsTry.branch]
          step
          step
          step
          let entry : module.Global := ⟨gt, init⟩
          refine ⟨?_, ⟨added ++ [entry], ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
          · scalar_tac
          · simp only [List.length_append, List.length_singleton]; scalar_tac
          · refine ⟨?_, ?_, ?_⟩
            · rw [henv.1]
            · simp only [v1_post, henv.2.1, List.append_assoc, entry]
            · simp [v_post, henv.2.2, List.append_assoc, entry]
          · exact hbytes.snoc (global_encoded hp hcb)
          · intro g hm
            rcases List.mem_append.mp hm with hm | hm
            · exact (hvalid g hm).append_globals [gt] v_post rfl
            · obtain rfl := List.mem_singleton.mp hm
              exact hcv.append_globals [gt] v_post rfl
          · simp only [v1_post, List.length_append, List.length_singleton]; omega
          · simp only [v_post, List.length_append, List.length_singleton]; omega
          · scalar_tac
  · exact ⟨by simp, [], by simp,
      ⟨by cases env; rfl, by simp, by simp⟩,
      ⟨[], .nil, Wasm.BytesAt.nil data start hstart⟩, by simp, hglobals, htypes⟩

@[step]
theorem module.decode_global_section.spec (data : Slice U8) (pos : Usize) (env : module.Env)
    (hglobals : env.globals.val.length ≤ pos.val)
    (htypes : env.global_types.val.length ≤ pos.val) :
    module.decode_global_section data pos env ⦃ r => match r.1 with
      | .Ok next => ∃ added, GlobalsAdded env r.2 added ∧
          At (VecEncoding GlobalEncoding) data pos added next ∧
          (∀ g ∈ added, ModuleConstants.Valid r.2 g.init g.gtype.valtype) ∧
          r.2.globals.val.length ≤ next.val ∧ r.2.global_types.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e => simp [module.decode_global_section, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    obtain ⟨count, start⟩ := pair
    have hs := hc.span
    obtain ⟨⟨r, result⟩, hloop, hp⟩ := WP.spec_imp_exists
      (module.decode_global_section_loop.spec data env count start hs.2.2 (by omega) (by omega))
    simp [module.decode_global_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
    rw [hloop]
    cases r with
    | Err e => simp
    | Ok next =>
      obtain ⟨added, hlen, henv, hb, ht, hg, hgt⟩ := hp
      exact ⟨added, henv, At.vector hc hb hlen, ht, hg, hgt⟩

end Itasca
