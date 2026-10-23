import Itasca.Module.Env.Dispatch

/-!
# Environment parser soundness

Specifications of the environment parser `module.validate_env` and its helpers
`module.validate_env_with` and `module.validate_env_with_loop`. For arbitrary input they terminate,
and a successful result carries the ordered `Run` of sections that produced the environment.
`module.validate_env.profile_spec` is the main result, and the unsuffixed `.spec` theorems are its
Wasm 1.0 instances.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleEnv

/-- Postcondition of the section loop for `profile`. An accepted result comes with a `Run` from the
initial state and a `Bounded` environment. -/
def LoopPostWith (profile : ValidationProfile) (data : Slice U8) (initial : module.Env) (decls : Declarations)
    (start : Usize) (initialId : U8) :
    core.result.Result (module.Env × Usize) error.Error → Prop
  | .Err _ => True
  | .Ok (env, next) => ∃ after last, Run (profile := profile) data initial decls start initialId env after next last ∧
      Bounded env next.val

/-- Postcondition of `module.validate_env` for `profile`. An accepted result comes with a fresh
environment, the module header bytes, a `Run` of sections from the header to the returned
position, and a `Bounded` environment. -/
def PostWith (profile : ValidationProfile) (data : Slice U8) : core.result.Result (module.Env × Usize) error.Error → Prop
  | .Err _ => True
  | .Ok (env, next) => ∃ initial start decls last,
      module.Env.new = .ok initial ∧
      Wasm1.BytesAt data 0#usize ModuleBinary.magicVersion start ∧
      Run (profile := profile) data initial {} start 0#u8 env decls next last ∧ Bounded env next.val

end Itasca.ModuleEnv

namespace Itasca

open ModuleBinary ModuleEnv

/-- The section loop either rejects or returns the ordered section history. Custom-section hooks
may reject, and they are only required to terminate. -/
theorem module.validate_env_with_loop.profile_spec {V : Type} (visitor : module.ModuleVisitor V)
    (htotal : ModuleTail.HooksTotal visitor) (data : Slice U8) (profile : ValidationProfile) (v : V)
    (env : module.Env) (decls : Declarations) (start : Usize) (initialId : U8)
    (hstart : start.val ≤ data.length) (hbound : Bounded env start.val) :
    module.validate_env_with_loop visitor data profile v env start initialId ⦃ r =>
      LoopPostWith profile data env decls start initialId r.1 ⦄ := by
  unfold module.validate_env_with_loop
  apply loop.spec_decr_nat (fun s => data.length - s.2.2.1.val)
    (fun s => ∃ currentDecls, Run (profile := profile) data env decls start initialId s.2.1 currentDecls s.2.2.1 s.2.2.2 ∧
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
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, LoopPostWith]
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
          | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, LoopPostWith]
          | Ok custom =>
            obtain ⟨nm, hn, hbefore, _, _⟩ := hp
            have hbytes := ModuleTail.custom_encoded (by simpa [hc, module.SECTION_CUSTOM] using hh) hn hbefore
            obtain ⟨⟨res, state'⟩, hvisit⟩ := htotal state custom
            simp [hvisit]
            cases res with
            | Err e => simp [LoopPostWith]
            | Ok u =>
              exact ⟨⟨currentDecls, .custom hrun hbytes⟩, hbound.mono (next := last.val) (by omega), by scalar_tac⟩
        · simp only [hc, ↓reduceIte]
          split
          · exact ⟨currentDecls, lastId, hrun, hbound⟩
          · split
            · exact ⟨currentDecls, lastId, hrun, hbound⟩
            · obtain ⟨rankResult, hrank, hrankPost⟩ := WP.spec_imp_exists (module.section_order.spec id)
              rw [hrank]
              cases rankResult with
              | Err e => simp [
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, LoopPostWith]
              | Ok rank =>
                obtain ⟨rfl, hidLow, hidHigh⟩ := hrankPost
                simp only [bind_ok]
                split
                · simp [LoopPostWith]
                · rename_i horder
                  have horder' : lastId.val < (sectionRank id).val := by scalar_tac
                  obtain ⟨⟨r, updated⟩, hread, hp⟩ := WP.spec_imp_exists
                    (module.decode_env_section.profile_spec data first id current currentDecls profile (hbound.mono (by omega)))
                  simp only [hread, bind_ok]
                  cases r with
                  | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, LoopPostWith]
                  | Ok next =>
                    obtain ⟨after, heffect, hbound⟩ := hp
                    simp
                    by_cases he : next = last
                    · subst next
                      simp only [↓reduceIte, WP.spec_ok]
                      exact ⟨⟨after, .step hrun horder' hh heffect⟩, hbound, by scalar_tac⟩
                    · have hn : next.val ≠ last.val := fun h => he (UScalar.eq_of_val_eq h)
                      simp [hn, LoopPostWith]
  · exact ⟨decls, .nil, hbound⟩

/-- `module.validate_env_with` reads the header, starts from the empty environment and runs the
section loop, so its result satisfies `PostWith`. -/
theorem module.validate_env_with.profile_spec {V : Type} (visitor : module.ModuleVisitor V)
    (htotal : ModuleTail.HooksTotal visitor) (data : Slice U8) (profile : ValidationProfile) (v : V) :
    module.validate_env_with visitor data profile v ⦃ r => ModuleEnv.PostWith profile data r.1 ⦄ := by
  obtain ⟨initial, hi, _, _, hb⟩ := WP.spec_imp_exists module.Env.new.spec
  obtain ⟨r, hr, hh⟩ := WP.spec_imp_exists (module.read_header.spec data)
  cases r with
  | Err e => simp [module.validate_env_with, hi, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, ModuleEnv.PostWith]
  | Ok start =>
    obtain ⟨⟨r, finalVisitor⟩, hloop, hp⟩ := WP.spec_imp_exists
      (module.validate_env_with_loop.profile_spec visitor htotal data profile v initial {} start 0#u8 hh.bound
        (hb.mono (Nat.zero_le _)))
    simp [module.validate_env_with, hi, hr, core.result.Result.Insts.CoreOpsTry.branch, hloop]
    cases r with
    | Err e => trivial
    | Ok pair =>
      obtain ⟨result, next⟩ := pair
      obtain ⟨decls, last, hrun, hbound⟩ := hp
      exact ⟨initial, start, decls, last, hi, hh, hrun, hbound⟩

/-- Arbitrary input bytes give an ordinary result from `module.validate_env`. A successful result
carries the complete ordered section history needed for declarative assembly. -/
theorem module.validate_env.profile_spec (data : Slice U8) (profile : ValidationProfile) :
    module.validate_env data profile ⦃ ModuleEnv.PostWith profile data ⦄ := by
  obtain ⟨⟨r, state⟩, hr, hp⟩ := WP.spec_imp_exists
    (module.validate_env_with.profile_spec module.EmptyModuleVisitor.Insts.ItascaModuleModuleVisitor
      ModuleTail.empty_hooks_total data profile ())
  simpa [module.validate_env, hr] using hp

end Itasca
