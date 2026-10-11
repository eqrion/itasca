import Itasca.Module.ModuleEnvDispatch

open Aeneas Aeneas.Std

namespace Itasca.ModuleEnv

def LoopPost (data : Slice U8) (initial : module.Env) (decls : Declarations)
    (start : Usize) (initialId : U8) :
    core.result.Result (module.Env × Usize) error.Error → Prop
  | .Err _ => True
  | .Ok (env, next) => ∃ after last, Run data initial decls start initialId env after next last ∧
      Bounded env next.val

def Post (data : Slice U8) : core.result.Result (module.Env × Usize) error.Error → Prop
  | .Err _ => True
  | .Ok (env, next) => ∃ initial start decls last,
      module.Env.new = .ok initial ∧
      Wasm.BytesAt data 0#usize ModuleBinary.magicVersion start ∧
      Run data initial {} start 0#u8 env decls next last ∧ Bounded env next.val

end Itasca.ModuleEnv

namespace Itasca

open ModuleBinary ModuleEnv

/-- The actual environment loop either rejects or returns the ordered section
history. Every custom callback may reject; only ordinary termination is required. -/
theorem module.validate_env_with_loop.spec {V : Type} (visitor : module.ModuleVisitor V)
    (htotal : ModuleTail.HooksTotal visitor) (data : Slice U8) (v : V)
    (env : module.Env) (decls : Declarations) (start : Usize) (initialId : U8)
    (hstart : start.val ≤ data.length) (hbound : Bounded env start.val) :
    module.validate_env_with_loop visitor data v env start initialId ⦃ r =>
      LoopPost data env decls start initialId r.1 ⦄ := by
  unfold module.validate_env_with_loop
  apply loop.spec_decr_nat (fun s => data.length - s.2.2.1.val)
    (fun s => ∃ currentDecls, Run data env decls start initialId s.2.1 currentDecls s.2.2.1 s.2.2.2 ∧
      Bounded s.2.1 s.2.2.1.val)
  · rintro ⟨state, current, pos, lastId⟩ ⟨currentDecls, hrun, hbound⟩
    dsimp only at hrun hbound
    have hpos := (hrun.span hstart).2
    unfold module.validate_env_with_loop.body
    dsimp only
    split
    · exact ⟨currentDecls, lastId, hrun, hbound⟩
    · rename_i hmore
      obtain ⟨r, hr, hh⟩ := WP.spec_imp_exists (module.read_section_header.spec data pos)
      rw [hr]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, LoopPost]
      | Ok triple =>
        obtain ⟨id, first, last⟩ := triple
        change SectionHeader data pos id first last at hh
        have hspan := hh.span
        simp [core.result.Result.Insts.CoreOpsTry.branch]
        by_cases hc : id = module.SECTION_CUSTOM
        · simp only [hc, ↓reduceIte]
          obtain ⟨r, hcustom, hp⟩ := WP.spec_imp_exists (module.decode_custom_section.spec data first last)
          rw [hcustom]
          cases r with
          | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, LoopPost]
          | Ok custom =>
            obtain ⟨nm, hn, hbefore, _, _⟩ := hp
            have hbytes := ModuleTail.custom_encoded (by simpa [hc, module.SECTION_CUSTOM] using hh) hn hbefore
            obtain ⟨⟨res, state'⟩, hvisit⟩ := htotal state custom
            simp [hvisit]
            cases res with
            | Err e => simp [LoopPost]
            | Ok u =>
              exact ⟨⟨currentDecls, .custom hrun hbytes⟩, hbound.mono (next := last.val) (by omega), by scalar_tac⟩
        · simp only [hc, ↓reduceIte]
          split
          · exact ⟨currentDecls, lastId, hrun, hbound⟩
          · split
            · simp [LoopPost]
            · rename_i horder
              have horder' : lastId.val < id.val := by scalar_tac
              obtain ⟨⟨r, updated⟩, hread, hp⟩ := WP.spec_imp_exists
                (module.decode_env_section.spec data first id current currentDecls (hbound.mono (by omega)))
              simp only [hread, bind_ok]
              cases r with
              | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, LoopPost]
              | Ok next =>
                obtain ⟨after, heffect, hbound⟩ := hp
                simp
                by_cases he : next = last
                · subst next
                  simp only [↓reduceIte, WP.spec_ok]
                  exact ⟨⟨after, .step hrun horder' hh heffect⟩, hbound, by scalar_tac⟩
                · have hn : next.val ≠ last.val := fun h => he (UScalar.eq_of_val_eq h)
                  simp [hn, LoopPost]
  · exact ⟨decls, .nil, hbound⟩

/-- Header checking and empty initialization discharge the loop's input bounds. -/
theorem module.validate_env_with.spec {V : Type} (visitor : module.ModuleVisitor V)
    (htotal : ModuleTail.HooksTotal visitor) (data : Slice U8) (v : V) :
    module.validate_env_with visitor data v ⦃ r => ModuleEnv.Post data r.1 ⦄ := by
  obtain ⟨initial, hi, _, _, hb⟩ := WP.spec_imp_exists module.Env.new.spec
  obtain ⟨r, hr, hh⟩ := WP.spec_imp_exists (module.read_header.spec data)
  cases r with
  | Err e => simp [module.validate_env_with, hi, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, ModuleEnv.Post]
  | Ok start =>
    obtain ⟨⟨r, finalVisitor⟩, hloop, hp⟩ := WP.spec_imp_exists
      (module.validate_env_with_loop.spec visitor htotal data v initial {} start 0#u8 hh.bound
        (hb.mono (Nat.zero_le _)))
    simp [module.validate_env_with, hi, hr, core.result.Result.Insts.CoreOpsTry.branch, hloop]
    cases r with
    | Err e => trivial
    | Ok pair =>
      obtain ⟨result, next⟩ := pair
      obtain ⟨decls, last, hrun, hbound⟩ := hp
      exact ⟨initial, start, decls, last, hi, hh, hrun, hbound⟩

/-- Arbitrary input bytes have an ordinary environment-parser result. Successful
results carry the complete ordered history needed for declarative assembly. -/
theorem module.validate_env.spec (data : Slice U8) :
    module.validate_env data ⦃ ModuleEnv.Post data ⦄ := by
  obtain ⟨⟨r, state⟩, hr, hp⟩ := WP.spec_imp_exists
    (module.validate_env_with.spec module.EmptyModuleVisitor.Insts.ItascaModuleModuleVisitor
      ModuleTail.empty_hooks_total data ())
  simpa [module.validate_env, hr] using hp

end Itasca
