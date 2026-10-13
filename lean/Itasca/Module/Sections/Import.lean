import Itasca.Module.Sections.Function
import Itasca.Module.Env.Declarations
import Itasca.Module.Readers.Names

set_option maxHeartbeats 800000

open Aeneas Aeneas.Std

namespace Itasca.ModuleSections

/-- A single import updates just its own index space, preserving declaration order. -/
def ImportAdded (env result : module.Env) (entry : module.Import)
    (profile : ValidationProfile := .Wasm1) : Prop :=
  result.imports.val = env.imports.val ++ [entry] ∧
  match entry.desc with
  | .Func idx => ∃ ft, ModuleEnv.Resolves env.types.val idx ft ∧
      result = { env with imports := result.imports, func_types := result.func_types, num_imported_funcs := result.num_imported_funcs } ∧
      result.func_types.val = env.func_types.val ++ [ft] ∧
      result.num_imported_funcs.val = env.num_imported_funcs.val + 1
  | .Global gt =>
      result = { env with imports := result.imports, global_types := result.global_types, num_imported_globals := result.num_imported_globals } ∧
      result.global_types.val = env.global_types.val ++ [gt] ∧
      result.num_imported_globals.val = env.num_imported_globals.val + 1 ∧
      ModuleBinary.ValueTypeAllowed profile gt.valtype
  | .Table tt =>
      result = { env with imports := result.imports, table_types := result.table_types } ∧
      result.table_types.val = env.table_types.val ++ [tt] ∧ (profile = .Wasm1 → result.table_types.val.length ≤ 1) ∧
      ModuleTranslation.LimitsValid tt.limits (2 ^ 32 - 1) ∧
      ModuleBinary.ElemTypeAllowed profile tt.elem
  | .Memory mt =>
      result = { env with imports := result.imports, mem_types := result.mem_types } ∧
      result.mem_types.val = env.mem_types.val ++ [mt] ∧ result.mem_types.val.length ≤ 1 ∧
      ModuleTranslation.LimitsValid mt.limits (2 ^ 16)

theorem import_encoded {data start p1 p2 next moduleName nm desc}
    (hm : ModuleBinary.At ModuleBinary.NameEncoding data start moduleName p1)
    (hn : ModuleBinary.At ModuleBinary.NameEncoding data p1 nm p2)
    (hd : ModuleBinary.At ModuleBinary.ImportDescEncoding data p2 desc next) :
    ModuleBinary.At ModuleBinary.ImportEncoding data start ⟨moduleName, nm, desc⟩ next := by
  obtain ⟨mb, hm, hs⟩ := hm
  obtain ⟨nb, hn, hns⟩ := hn
  obtain ⟨db, hd, hds⟩ := hd
  exact ⟨mb ++ nb ++ db, ⟨mb, nb, db, hm, hn, hd, rfl⟩, (hs.append hns).append hds⟩

end Itasca.ModuleSections

namespace Itasca

open ModuleBinary ModuleSections

@[step]
theorem module.decode_import.spec (data : Slice U8) (pos : Usize) (env : module.Env)
    (hbound : ModuleEnv.Bounded env pos.val) (profile : ValidationProfile := .Wasm1) :
    module.decode_import data pos env profile ⦃ r => match r.1 with
      | .Ok next => ∃ entry, ImportAdded env r.2 entry profile ∧
          At ImportEncoding data pos (ModuleEnv.rawImport entry) next ∧
          ModuleEnv.Bounded r.2 next.val
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hm⟩ := WP.spec_imp_exists (module.decode_name.spec data pos)
  cases r with
  | Err e => simp [module.decode_import, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨modname, p1⟩ := pair
    obtain ⟨r, hn, hname⟩ := WP.spec_imp_exists (module.decode_name.spec data p1)
    cases r with
    | Err e => simp [module.decode_import, hr, hn, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok pair =>
      obtain ⟨nm, p2⟩ := pair
      obtain ⟨r, hk, hkind⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data p2)
      cases r with
      | Err e => simp [module.decode_import, hr, hn, hk, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          error.Error.Insts.CoreConvertFromOpError.from]
      | Ok pair =>
        obtain ⟨kind, p3⟩ := pair
        have hspanM := hm.span
        have hspanN := hname.span
        have hspanK := (At.byte hkind).length
        have hspanB := (At.byte hkind).bound
        have hprogress : pos.val < p3.val := by simp only [List.length_singleton] at hspanK; omega
        cases hbound
        simp [module.decode_import, hr, hn, hk, core.result.Result.Insts.CoreOpsTry.branch]
        split
        · obtain ⟨r, hd, hdesc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data p3)
          cases r with
          | Err e => simp [hd,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              error.Error.Insts.CoreConvertFromOpError.from]
          | Ok pair =>
            obtain ⟨value, next⟩ := pair
            have hspanD := hdesc.span
            obtain ⟨r, ht, hlookup⟩ := WP.spec_imp_exists (module.lookup_type.spec env value)
            cases r with
            | Err e => simp [hd, ht,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            | Ok ft =>
              have hcapacity : env.func_types.val.length < Usize.max := by scalar_tac
              have hcapacityI : env.imports.val.length < Usize.max := by scalar_tac
              have hcapacityN : env.num_imported_funcs.val < Usize.max := by scalar_tac
              simp [hd, ht]
              step
              step
              step
              let entry : module.Import := ⟨modname, nm, .Func value⟩
              refine ⟨entry, ?_, ?_, ?_⟩
              · refine ⟨v1_post, ft, hlookup, rfl, v_post, i_post⟩
              · apply import_encoded hm hname
                apply At.prepend (by with_unfolding_all exact hkind) (At.of_u32 hdesc)
                intro bytes hbytes
                exact .func value hbytes
              · constructor <;> simp only [v_post, v1_post, List.length_append, List.length_singleton] <;> scalar_tac
        · obtain ⟨r, hd, hdesc⟩ := WP.spec_imp_exists (module.decode_table_type.allowed_spec data p3 profile)
          cases r with
          | Err e => simp [hd,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok pair =>
            obtain ⟨value, next⟩ := pair
            obtain ⟨⟨hdesc, hlimits⟩, hallowed⟩ := hdesc
            have hspanD := hdesc.span
            have hcapacity : env.table_types.val.length < Usize.max := by scalar_tac
            have hcapacityI : env.imports.val.length < Usize.max := by scalar_tac
            simp [hd]
            step
            obtain ⟨checked, hchecked, hcount⟩ := WP.spec_imp_exists
              (module.check_table_count.spec { env with table_types := v } profile)
            rw [hchecked]
            cases checked with
            | Err e => simp [
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            | Ok u =>
              cases u
              simp only [bind_ok]
              step
              let entry : module.Import := ⟨modname, nm, .Table value⟩
              refine ⟨entry, ?_, ?_, ?_⟩
              · refine ⟨v1_post, rfl, v_post, ?_, ?_, hallowed⟩
                · exact hcount
                · simpa [ModuleTranslation.LimitsValid, ModuleBinary.LimitsValid, Option.mem_def, global_simps, U32.rMax] using hlimits
              · apply import_encoded hm hname
                apply At.prepend (by with_unfolding_all exact hkind) hdesc
                intro bytes hbytes
                exact .table value hbytes
              · constructor <;> simp only [v_post, v1_post, List.length_append, List.length_singleton] <;> scalar_tac
        · obtain ⟨r, hd, hdesc⟩ := WP.spec_imp_exists (module.decode_mem_type.spec data p3)
          cases r with
          | Err e => simp [hd,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok pair =>
            obtain ⟨value, next⟩ := pair
            obtain ⟨hdesc, hlimits⟩ := hdesc
            have hspanD := hdesc.span
            have hcapacity : env.mem_types.val.length < Usize.max := by scalar_tac
            have hcapacityI : env.imports.val.length < Usize.max := by scalar_tac
            simp [hd]
            step
            split
            · simp
            · rename_i hcount
              step
              let entry : module.Import := ⟨modname, nm, .Memory value⟩
              refine ⟨entry, ?_, ?_, ?_⟩
              · refine ⟨v1_post, rfl, v_post, ?_, ?_⟩
                · simpa [global_simps] using hcount
                · simpa [ModuleTranslation.LimitsValid, ModuleBinary.LimitsValid, Option.mem_def, global_simps, U32.rMax] using hlimits
              · apply import_encoded hm hname
                apply At.prepend (by with_unfolding_all exact hkind) hdesc
                intro bytes hbytes
                exact .memory value hbytes
              · constructor <;> simp only [v_post, v1_post, List.length_append, List.length_singleton] <;> scalar_tac
        · obtain ⟨r, hd, hdesc⟩ := WP.spec_imp_exists (module.decode_global_type.allowed_spec data p3 profile)
          cases r with
          | Err e => simp [hd,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok pair =>
            obtain ⟨value, next⟩ := pair
            obtain ⟨hdesc, hallowed⟩ := hdesc
            have hspanD := hdesc.span
            have hcapacity : env.global_types.val.length < Usize.max := by scalar_tac
            have hcapacityI : env.imports.val.length < Usize.max := by scalar_tac
            have hcapacityN : env.num_imported_globals.val < Usize.max := by scalar_tac
            simp [hd]
            step
            step
            step
            let entry : module.Import := ⟨modname, nm, .Global value⟩
            refine ⟨entry, ?_, ?_, ?_⟩
            · exact ⟨v1_post, rfl, v_post, i_post, hallowed⟩
            · apply import_encoded hm hname
              apply At.prepend (by with_unfolding_all exact hkind) hdesc
              intro bytes hbytes
              exact .global value hbytes
            · constructor <;> simp only [v_post, v1_post, List.length_append, List.length_singleton] <;> scalar_tac
        · simp

end Itasca
