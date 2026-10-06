import Itasca.ModuleReaders

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary

/-- The public module header reader checks the exact magic and version bytes. -/
theorem module.read_header.spec (data : Slice U8) :
    module.read_header data ⦃ r => match r with
      | .Ok next => Wasm.BytesAt data 0#usize magicVersion next
      | .Err _ => True ⦄ := by
  obtain ⟨r, h1, hb1⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data 0#usize)
  cases r with
  | Err e =>
      simp [module.read_header, h1, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        error.Error.Insts.CoreConvertFromOpError.from]
      all_goals split_ifs <;> simp
  | Ok pair =>
      obtain ⟨b1, p1⟩ := pair
      obtain ⟨r, h2, hb2⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data p1)
      cases r with
      | Err e =>
          simp [module.read_header, h1, h2, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            error.Error.Insts.CoreConvertFromOpError.from]
          all_goals split_ifs <;> simp
      | Ok pair =>
          obtain ⟨b2, p2⟩ := pair
          obtain ⟨r, h3, hb3⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data p2)
          cases r with
          | Err e =>
              simp [module.read_header, h1, h2, h3, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                error.Error.Insts.CoreConvertFromOpError.from]
              all_goals split_ifs <;> simp
          | Ok pair =>
              obtain ⟨b3, p3⟩ := pair
              obtain ⟨r, h4, hb4⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data p3)
              cases r with
              | Err e =>
                  simp [module.read_header, h1, h2, h3, h4, core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                    error.Error.Insts.CoreConvertFromOpError.from]
                  all_goals split_ifs <;> simp
              | Ok pair =>
                  obtain ⟨b4, p4⟩ := pair
                  obtain ⟨r, h5, hb5⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data p4)
                  cases r with
                  | Err e =>
                      simp [module.read_header, h1, h2, h3, h4, h5, core.result.Result.Insts.CoreOpsTry.branch,
                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                        error.Error.Insts.CoreConvertFromOpError.from]
                      all_goals split_ifs <;> simp
                  | Ok pair =>
                      obtain ⟨b5, p5⟩ := pair
                      obtain ⟨r, h6, hb6⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data p5)
                      cases r with
                      | Err e =>
                          simp [module.read_header, h1, h2, h3, h4, h5, h6, core.result.Result.Insts.CoreOpsTry.branch,
                            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                            error.Error.Insts.CoreConvertFromOpError.from]
                          all_goals split_ifs <;> simp
                      | Ok pair =>
                          obtain ⟨b6, p6⟩ := pair
                          obtain ⟨r, h7, hb7⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data p6)
                          cases r with
                          | Err e =>
                              simp [module.read_header, h1, h2, h3, h4, h5, h6, h7, core.result.Result.Insts.CoreOpsTry.branch,
                                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                                error.Error.Insts.CoreConvertFromOpError.from]
                              all_goals split_ifs <;> simp
                          | Ok pair =>
                              obtain ⟨b7, p7⟩ := pair
                              obtain ⟨r, h8, hb8⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data p7)
                              cases r with
                              | Err e =>
                                  simp [module.read_header, h1, h2, h3, h4, h5, h6, h7, h8, core.result.Result.Insts.CoreOpsTry.branch,
                                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                                    error.Error.Insts.CoreConvertFromOpError.from]
                                  all_goals split_ifs <;> simp
                              | Ok pair =>
                                  obtain ⟨b8, p8⟩ := pair
                                  simp [module.read_header, h1, h2, h3, h4, h5, h6, h7, h8,
                                    core.result.Result.Insts.CoreOpsTry.branch]
                                  split_ifs <;> simp_all
                                  have hbytes := ((((((((At.byte hb1).append (At.byte hb2)).append (At.byte hb3)).append (At.byte hb4)).append (At.byte hb5)).append (At.byte hb6)).append (At.byte hb7)).append (At.byte hb8))
                                  have heq : [b1, b2, b3, b4, b5, b6, b7, b8] = magicVersion := by
                                    simp only [magicVersion, List.cons.injEq]
                                    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> apply UScalar.eq_of_val_eq <;> scalar_tac
                                  simpa [heq] using hbytes

end Itasca
