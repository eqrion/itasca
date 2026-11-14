import Itasca.Module.Sections.ElementHeader
import Itasca.Module.Const.Parser
import Itasca.Module.Env.Declarations
import Itasca.Module.Readers.TypesComplete
import Itasca.Module.Elab.SegmentTyping
import Itasca.Module.Readers.Utf8
import Itasca.Module.Sections.Data
import Itasca.Contracts

/-!
Sections, each formerly its own module: Global, Function, Import, Imports, Element, Tail.
-/

/-! ## Global -/

section

/-!
# Global section parser

Soundness of `metadata.decode_global_section` and its loop. `GlobalsAdded` says the environment
gains the decoded globals, their types and the function references their initializers declare.
The span is a `VecEncoding GlobalEncoding` and each initializer is `ModuleConstants.Valid` at its
global's type. Completeness is in `Module/Sections/GlobalComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleConstants

/-- Constant validity is preserved when globals are appended after the imported ones. -/
theorem Valid.append_globals {env result e t} (h : Valid env e t)
    (suffix : List wasm_types.GlobalType)
    (hglobals : result.global_types.val = env.global_types.val ++ suffix)
    (hcount : result.num_imported_globals = env.num_imported_globals)
    (hfuncs : result.func_types = env.func_types) : Valid result e t := by
  cases h with
  | i32 value => exact .i32 value
  | i64 value => exact .i64 value
  | f32 value => exact .f32 value
  | f64 value => exact .f64 value
  | v128 low high => exact .v128 low high
  | refNull ty => exact .refNull ty
  | refFunc idx hi => exact .refFunc idx (by simpa [hfuncs] using hi)
  | globalGet idx gt hi hgt himport hconst =>
    have hi' : idx.val < result.global_types.val.length := by simp [hglobals]; omega
    exact Valid.globalGet idx gt hi'
      (by simpa only [hglobals, List.getElem_append_left hi] using hgt)
      (by simpa [hcount] using himport) hconst

end Itasca.ModuleConstants

namespace Itasca.ModuleSections

/-- `result` is `env` with the globals `added` appended to the globals and global types, and the
function references of their initializers appended to the declared functions. Nothing else
changes. -/
def GlobalsAdded (env result : metadata.Env) (added : List metadata.Global) : Prop :=
  result = { env with globals := result.globals, global_types := result.global_types, declared_funcs := result.declared_funcs } ∧
  result.globals.val = env.globals.val ++ added ∧
  result.global_types.val = env.global_types.val ++ added.map metadata.Global.gtype ∧
  result.declared_funcs.val = env.declared_funcs.val ++ added.flatMap ModuleReferences.global

/-- A global type and an initializer span in sequence form a `GlobalEncoding`. -/
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

/-- The global loop adds `count` globals forming a `Rep GlobalEncoding` span, with valid
initializers. -/
@[step]
theorem metadata.decode_global_section_loop.spec (data : Slice U8) (env : metadata.Env)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hglobals : env.globals.val.length ≤ start.val)
    (htypes : env.global_types.val.length ≤ start.val)
    (hreferences : env.declared_funcs.val.length ≤ start.val) :
    metadata.decode_global_section_loop data env count start 0#u32 ⦃ r => match r.1 with
      | .Ok next => ∃ added, added.length = count.val ∧ GlobalsAdded env r.2 added ∧
          At (Rep GlobalEncoding) data start added next ∧
          (∀ g ∈ added, ModuleConstants.Valid r.2 g.init g.gtype.valtype) ∧
          r.2.globals.val.length ≤ next.val ∧ r.2.global_types.val.length ≤ next.val ∧
          r.2.declared_funcs.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  unfold metadata.decode_global_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ ∃ added, added.length = s.2.2.val ∧
      GlobalsAdded env s.1 added ∧ At (Rep GlobalEncoding) data start added s.2.1 ∧
      (∀ g ∈ added, ModuleConstants.Valid s.1 g.init g.gtype.valtype) ∧
      s.1.globals.val.length ≤ s.2.1.val ∧ s.1.global_types.val.length ≤ s.2.1.val ∧
      s.1.declared_funcs.val.length ≤ s.2.1.val)
  · rintro ⟨current, pos, i⟩ ⟨hi, added, hlen, henv, hbytes, hvalid, hglobals, htypes, hreferences⟩
    dsimp only at hi hlen henv hbytes hvalid hglobals htypes hreferences
    unfold metadata.decode_global_section_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : i.val = count.val := by scalar_tac
      exact ⟨added, by omega, henv, hbytes, hvalid, hglobals, htypes, hreferences⟩
    · rename_i hmore
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (metadata.decode_global_type.spec data pos)
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
        obtain ⟨r, hc, hconst⟩ := WP.spec_imp_exists (metadata.decode_const_expr.spec data middle current gt.valtype)
        cases r with
        | Err e => simp [hc, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok pair =>
          obtain ⟨init, next⟩ := pair
          obtain ⟨hcb, hcv⟩ := hconst
          have hs := hcb.span
          have hcapacity : current.global_types.val.length < Usize.max := by scalar_tac
          have hcapacity' : current.globals.val.length < Usize.max := by scalar_tac
          have hcapacityRefs : current.declared_funcs.val.length < Usize.max := by scalar_tac
          simp [hc, core.result.Result.Insts.CoreOpsTry.branch]
          step as ⟨declared, hdeclared⟩
          have hdstate := hdeclared.1
          rw [hdstate]
          clear hdstate
          step
          step
          step
          let entry : metadata.Global := ⟨gt, init⟩
          refine ⟨?_, ⟨added ++ [entry], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
          · scalar_tac
          · simp only [List.length_append, List.length_singleton]; scalar_tac
          · refine ⟨?_, ?_, ?_, ?_⟩
            · rw [henv.1]
            · simp only [v1_post, henv.2.1, List.append_assoc, entry]
            · simp [v_post, henv.2.2.1, List.append_assoc, entry]
            · simp [hdeclared.2, henv.2.2.2, List.flatMap_append,
                ModuleReferences.global, entry, List.append_assoc]
          · exact hbytes.snoc (global_encoded hp hcb)
          · intro g hm
            rcases List.mem_append.mp hm with hm | hm
            · exact (hvalid g hm).append_globals [gt] v_post rfl rfl
            · obtain rfl := List.mem_singleton.mp hm
              exact hcv.append_globals [gt] v_post rfl rfl
          · simp only [v1_post, List.length_append, List.length_singleton]; omega
          · simp only [v_post, List.length_append, List.length_singleton]; omega
          · have hlen : (ModuleReferences.initializer init).length ≤ 1 := by
              cases init <;> simp [ModuleReferences.initializer]
            simp only [hdeclared.2, List.length_append]
            omega
          · scalar_tac
  · exact ⟨by simp, [], by simp,
      ⟨by cases env; rfl, by simp, by simp, by simp⟩,
      ⟨[], .nil, Wasm1.BytesAt.nil data start hstart⟩, by simp, hglobals, htypes, hreferences⟩

/-- `metadata.decode_global_section` adds the globals of a `VecEncoding GlobalEncoding` span, with
valid initializers. -/
@[step]
theorem metadata.decode_global_section.spec (data : Slice U8) (pos : Usize) (env : metadata.Env)
    (hglobals : env.globals.val.length ≤ pos.val)
    (htypes : env.global_types.val.length ≤ pos.val)
    (hreferences : env.declared_funcs.val.length ≤ pos.val) :
    metadata.decode_global_section data pos env ⦃ r => match r.1 with
      | .Ok next => ∃ added, GlobalsAdded env r.2 added ∧
          At (VecEncoding GlobalEncoding) data pos added next ∧
          (∀ g ∈ added, ModuleConstants.Valid r.2 g.init g.gtype.valtype) ∧
          r.2.globals.val.length ≤ next.val ∧ r.2.global_types.val.length ≤ next.val ∧
          r.2.declared_funcs.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e => simp [metadata.decode_global_section, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    obtain ⟨count, start⟩ := pair
    have hs := hc.span
    obtain ⟨⟨r, result⟩, hloop, hp⟩ := WP.spec_imp_exists
      (metadata.decode_global_section_loop.spec data env count start hs.2.2 (by omega) (by omega) (by omega))
    simp [metadata.decode_global_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
    rw [hloop]
    cases r with
    | Err e => simp
    | Ok next =>
      obtain ⟨added, hlen, henv, hb, ht, hg, hgt, href⟩ := hp
      exact ⟨added, henv, At.vector hc hb hlen, ht, hg, hgt, href⟩

end Itasca

end

/-! ## Function -/

section

/-!
# Function section parser

Soundness of `metadata.decode_function_section` and its loop. `FunctionsAdded` says the environment
gains the decoded type indices and the signatures they resolve to, in order. The decoded span is
a `VecEncoding IndexEncoding`. Completeness is in `Module/Sections/FunctionComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleSections

/-- `result` is `env` with `indices` appended to the function type indices and the resolved
`signatures` appended to the function types, and nothing else changed. -/
def FunctionsAdded (env result : metadata.Env) (indices : List U32)
    (signatures : List wasm_types.FuncType) : Prop :=
  result = { env with func_type_indices := result.func_type_indices, func_types := result.func_types } ∧
    result.func_type_indices.val = env.func_type_indices.val ++ indices ∧
    result.func_types.val = env.func_types.val ++ signatures ∧
    List.Forall₂ (ModuleEnv.Resolves env.types.val) indices signatures

end Itasca.ModuleSections

namespace Itasca

open ModuleBinary ModuleSections

/-- The function loop adds `count` indices forming a `Rep IndexEncoding` span. -/
@[step]
theorem metadata.decode_function_section_loop.spec (data : Slice U8) (env : metadata.Env)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hfuncs : env.func_types.val.length ≤ start.val)
    (hindices : env.func_type_indices.val.length ≤ start.val) :
    metadata.decode_function_section_loop data env count start 0#u32 ⦃ r => match r.1 with
      | .Ok next => ∃ indices signatures, indices.length = count.val ∧
          FunctionsAdded env r.2 indices signatures ∧
          At (Rep IndexEncoding) data start indices next ∧
          r.2.func_types.val.length ≤ next.val ∧ r.2.func_type_indices.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  unfold metadata.decode_function_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ ∃ indices signatures,
      indices.length = s.2.2.val ∧ FunctionsAdded env s.1 indices signatures ∧
      At (Rep IndexEncoding) data start indices s.2.1 ∧
      s.1.func_types.val.length ≤ s.2.1.val ∧ s.1.func_type_indices.val.length ≤ s.2.1.val)
  · rintro ⟨current, pos, i⟩ ⟨hi, indices, signatures, hlen, henv, hbytes, hfuncs, hindices⟩
    dsimp only at hi hlen henv hbytes hfuncs hindices
    unfold metadata.decode_function_section_loop.body
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
        obtain ⟨r, ht, hlookup⟩ := WP.spec_imp_exists (metadata.lookup_type.spec current idx)
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

/-- `metadata.decode_function_section` adds the indices of a `VecEncoding IndexEncoding` span with
their resolved signatures. -/
@[step]
theorem metadata.decode_function_section.spec (data : Slice U8) (pos : Usize) (env : metadata.Env)
    (hfuncs : env.func_types.val.length ≤ pos.val)
    (hindices : env.func_type_indices.val.length ≤ pos.val) :
    metadata.decode_function_section data pos env ⦃ r => match r.1 with
      | .Ok next => ∃ indices signatures, FunctionsAdded env r.2 indices signatures ∧
          At (VecEncoding IndexEncoding) data pos indices next ∧
          r.2.func_types.val.length ≤ next.val ∧ r.2.func_type_indices.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e => simp [metadata.decode_function_section, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    obtain ⟨count, start⟩ := pair
    have hs := hc.span
    obtain ⟨⟨r, result⟩, hloop, hp⟩ := WP.spec_imp_exists
      (metadata.decode_function_section_loop.spec data env count start hs.2.2 (by omega) (by omega))
    simp [metadata.decode_function_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
    rw [hloop]
    cases r with
    | Err e => simp
    | Ok next =>
      obtain ⟨indices, signatures, hlen, henv, hb, hf, hi⟩ := hp
      exact ⟨indices, ⟨signatures, henv⟩, At.vector hc hb hlen, hf, hi⟩

end Itasca

end

/-! ## Import -/

section

/-!
# Single import parser

Soundness of `metadata.decode_import`. `ImportAdded` says that the environment gains the import
and updates only the index space of its kind, with the limits and memory count checks of
that kind. The decoded bytes are an `ImportEncoding` span and the environment stays `Bounded`.
Completeness is in `Module/Sections/ImportsComplete`.
-/

set_option maxHeartbeats 800000

open Aeneas Aeneas.Std

namespace Itasca.ModuleSections

/-- `result` is `env` with `entry` appended to the imports and to the index space of its kind.
Functions must resolve their type, tables and memories satisfy their limits, and memories
respect the count cap. -/
def ImportAdded (env result : metadata.Env) (entry : metadata.Import) : Prop :=
  result.imports.val = env.imports.val ++ [entry] ∧
  match entry.desc with
  | .Func idx => ∃ ft, ModuleEnv.Resolves env.types.val idx ft ∧
      result = { env with imports := result.imports, func_types := result.func_types, num_imported_funcs := result.num_imported_funcs } ∧
      result.func_types.val = env.func_types.val ++ [ft] ∧
      result.num_imported_funcs.val = env.num_imported_funcs.val + 1
  | .Global gt =>
      result = { env with imports := result.imports, global_types := result.global_types, num_imported_globals := result.num_imported_globals } ∧
      result.global_types.val = env.global_types.val ++ [gt] ∧
      result.num_imported_globals.val = env.num_imported_globals.val + 1
  | .Table tt =>
      result = { env with imports := result.imports, table_types := result.table_types } ∧
      result.table_types.val = env.table_types.val ++ [tt] ∧
      ModuleTranslation.LimitsValid tt.limits (2 ^ 32 - 1)
  | .Memory mt =>
      result = { env with imports := result.imports, mem_types := result.mem_types } ∧
      result.mem_types.val = env.mem_types.val ++ [mt] ∧ result.mem_types.val.length ≤ 1 ∧
      ModuleTranslation.LimitsValid mt.limits (2 ^ 16)

/-- A module name, an import name and a descriptor span in sequence form an `ImportEncoding`. -/
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

/-- `metadata.decode_import` adds one import to the environment (`ImportAdded`), the bytes are its
`ImportEncoding` span, and the environment stays within the byte bound. -/
@[step]
theorem metadata.decode_import.spec (data : Slice U8) (pos : Usize) (env : metadata.Env)
    (hbound : ModuleEnv.Bounded env pos.val) :
    metadata.decode_import data pos env ⦃ r => match r.1 with
      | .Ok next => ∃ entry, ImportAdded env r.2 entry ∧
          At ImportEncoding data pos (ModuleEnv.rawImport entry) next ∧
          ModuleEnv.Bounded r.2 next.val
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hm⟩ := WP.spec_imp_exists (metadata.decode_name.spec data pos)
  cases r with
  | Err e => simp [metadata.decode_import, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨modname, p1⟩ := pair
    obtain ⟨r, hn, hname⟩ := WP.spec_imp_exists (metadata.decode_name.spec data p1)
    cases r with
    | Err e => simp [metadata.decode_import, hr, hn, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok pair =>
      obtain ⟨nm, p2⟩ := pair
      obtain ⟨r, hk, hkind⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data p2)
      cases r with
      | Err e => simp [metadata.decode_import, hr, hn, hk, core.result.Result.Insts.CoreOpsTry.branch,
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
        simp [metadata.decode_import, hr, hn, hk, core.result.Result.Insts.CoreOpsTry.branch]
        split
        · obtain ⟨r, hd, hdesc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data p3)
          cases r with
          | Err e => simp [hd,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              error.Error.Insts.CoreConvertFromOpError.from]
          | Ok pair =>
            obtain ⟨value, next⟩ := pair
            have hspanD := hdesc.span
            obtain ⟨r, ht, hlookup⟩ := WP.spec_imp_exists (metadata.lookup_type.spec env value)
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
              let entry : metadata.Import := ⟨modname, nm, .Func value⟩
              refine ⟨entry, ?_, ?_, ?_⟩
              · refine ⟨v1_post, ft, hlookup, rfl, v_post, i_post⟩
              · apply import_encoded hm hname
                apply At.prepend (by with_unfolding_all exact hkind) (At.of_u32 hdesc)
                intro bytes hbytes
                exact .func value hbytes
              · constructor <;> simp only [v_post, v1_post, List.length_append, List.length_singleton] <;> scalar_tac
        · obtain ⟨r, hd, hdesc⟩ := WP.spec_imp_exists (metadata.decode_table_type.spec data p3)
          cases r with
          | Err e => simp [hd,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok pair =>
            obtain ⟨value, next⟩ := pair
            obtain ⟨hdesc, hlimits⟩ := hdesc
            have hspanD := hdesc.span
            have hcapacity : env.table_types.val.length < Usize.max := by scalar_tac
            have hcapacityI : env.imports.val.length < Usize.max := by scalar_tac
            simp [hd]
            step
            step
            let entry : metadata.Import := ⟨modname, nm, .Table value⟩
            refine ⟨entry, ?_, ?_, ?_⟩
            · refine ⟨v1_post, rfl, v_post, ?_⟩
              simpa [ModuleTranslation.LimitsValid, ModuleBinary.LimitsValid, Option.mem_def, global_simps, U32.rMax] using hlimits
            · apply import_encoded hm hname
              apply At.prepend (by with_unfolding_all exact hkind) hdesc
              intro bytes hbytes
              exact .table value hbytes
            · constructor <;> simp only [v_post, v1_post, List.length_append, List.length_singleton] <;> scalar_tac
        · obtain ⟨r, hd, hdesc⟩ := WP.spec_imp_exists (metadata.decode_mem_type.spec data p3)
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
              let entry : metadata.Import := ⟨modname, nm, .Memory value⟩
              refine ⟨entry, ?_, ?_, ?_⟩
              · refine ⟨v1_post, rfl, v_post, ?_, ?_⟩
                · simpa [global_simps] using hcount
                · simpa [ModuleTranslation.LimitsValid, ModuleBinary.LimitsValid, Option.mem_def, global_simps, U32.rMax] using hlimits
              · apply import_encoded hm hname
                apply At.prepend (by with_unfolding_all exact hkind) hdesc
                intro bytes hbytes
                exact .memory value hbytes
              · constructor <;> simp only [v_post, v1_post, List.length_append, List.length_singleton] <;> scalar_tac
        · obtain ⟨r, hd, hdesc⟩ := WP.spec_imp_exists (metadata.decode_global_type.spec data p3)
          cases r with
          | Err e => simp [hd,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok pair =>
            obtain ⟨value, next⟩ := pair
            have hspanD := hdesc.span
            have hcapacity : env.global_types.val.length < Usize.max := by scalar_tac
            have hcapacityI : env.imports.val.length < Usize.max := by scalar_tac
            have hcapacityN : env.num_imported_globals.val < Usize.max := by scalar_tac
            simp [hd]
            step
            step
            step
            let entry : metadata.Import := ⟨modname, nm, .Global value⟩
            refine ⟨entry, ?_, ?_, ?_⟩
            · exact ⟨v1_post, rfl, v_post, i_post⟩
            · apply import_encoded hm hname
              apply At.prepend (by with_unfolding_all exact hkind) hdesc
              intro bytes hbytes
              exact .global value hbytes
            · constructor <;> simp only [v_post, v1_post, List.length_append, List.length_singleton] <;> scalar_tac
        · simp

end Itasca

end

/-! ## Imports -/

section

/-!
# Import section parser

Soundness of `metadata.decode_import_section` and its loop. `ImportsAdded` is the ordered sequence
of `ImportAdded` updates. The
decoded span is a `VecEncoding ImportEncoding` of the raw imports. Completeness is in
`Module/Sections/ImportsComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleSections

/-- `result` is `initial` after adding `entries` one at a time by `ImportAdded`. -/
inductive ImportsAdded (initial : metadata.Env) : List metadata.Import → metadata.Env →
    Prop where
  | nil : ImportsAdded initial [] initial
  | snoc {entries before after entry} : ImportsAdded initial entries before →
      ImportAdded before after entry → ImportsAdded initial (entries ++ [entry]) after

end Itasca.ModuleSections

namespace Itasca

open ModuleBinary ModuleSections

/-- The import loop adds `count` imports forming a `Rep ImportEncoding` span. -/
@[step]
theorem metadata.decode_import_section_loop.spec (data : Slice U8) (env : metadata.Env)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hbound : ModuleEnv.Bounded env start.val) :
    metadata.decode_import_section_loop data env count start 0#u32 ⦃ r => match r.1 with
      | .Ok next => ∃ entries, entries.length = count.val ∧ ImportsAdded env entries r.2 ∧
          At (Rep ImportEncoding) data start (entries.map ModuleEnv.rawImport) next ∧
          ModuleEnv.Bounded r.2 next.val
      | .Err _ => True ⦄ := by
  unfold metadata.decode_import_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ ∃ entries, entries.length = s.2.2.val ∧
      ImportsAdded env entries s.1 ∧
      At (Rep ImportEncoding) data start (entries.map ModuleEnv.rawImport) s.2.1 ∧
      ModuleEnv.Bounded s.1 s.2.1.val)
  · rintro ⟨current, pos, i⟩ ⟨hi, entries, hlen, henv, hbytes, hbound⟩
    dsimp only at hi hlen henv hbytes hbound
    unfold metadata.decode_import_section_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : i.val = count.val := by scalar_tac
      exact ⟨entries, by omega, henv, hbytes, hbound⟩
    · rename_i hmore
      obtain ⟨⟨r, updated⟩, hr, hp⟩ := WP.spec_imp_exists (metadata.decode_import.spec data pos current hbound)
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
      ⟨[], .nil, Wasm1.BytesAt.nil data start hstart⟩, hbound⟩

/-- `metadata.decode_import_section` adds the imports of a `VecEncoding ImportEncoding` span. -/
@[step]
theorem metadata.decode_import_section.spec (data : Slice U8) (pos : Usize) (env : metadata.Env)
    (hbound : ModuleEnv.Bounded env pos.val) :
    metadata.decode_import_section data pos env ⦃ r => match r.1 with
      | .Ok next => ∃ entries, ImportsAdded env entries r.2 ∧
          At (VecEncoding ImportEncoding) data pos (entries.map ModuleEnv.rawImport) next ∧
          ModuleEnv.Bounded r.2 next.val
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e => simp [metadata.decode_import_section, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    obtain ⟨count, start⟩ := pair
    have hs := hc.span
    obtain ⟨⟨r, result⟩, hloop, hp⟩ := WP.spec_imp_exists
      (metadata.decode_import_section_loop.spec data env count start hs.2.2 (hbound.mono (by omega)))
    simp [metadata.decode_import_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
    rw [hloop]
    cases r with
    | Err e => simp
    | Ok next =>
      obtain ⟨entries, hlen, henv, hb, hbound⟩ := hp
      exact ⟨entries, henv, At.vector hc hb (by simpa using hlen), hbound⟩

end Itasca

end

/-! ## Element -/

section

/-!
# Element section parser

Soundness of `metadata.decode_element_section`, its loop and `metadata.decode_func_indices`.
`ElementsAdded` says the environment gains the decoded elements and their function references. The
span is a `VecEncoding (ElementEncodingFor)` and every element is `ElementValid`. The
`element_encoded` lemmas build element encodings from their parts. Completeness is in
`Module/Sections/ElementComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary ModuleSections

end Itasca

namespace Itasca.ModuleSections

/-- `result` is `env` with the elements `added` appended and their function references appended to
the declared functions. Nothing else changes. -/
def ElementsAdded (env result : metadata.Env) (added : List metadata.Element) : Prop :=
  result = { env with elements := result.elements, declared_funcs := result.declared_funcs } ∧
  result.elements.val = env.elements.val ++ added ∧
  result.declared_funcs.val = env.declared_funcs.val ++ added.flatMap ModuleReferences.element

/-- An element is valid in the environment: its table, offset and initializers are valid. -/
abbrev ElementValid := ModuleSegments.elementValid

end Itasca.ModuleSections

namespace Itasca

open ModuleBinary ModuleSections

private theorem element_valid_caches {env result entry}
    (h : ElementValid result entry)
    (hf : env.func_types = result.func_types) (hg : env.global_types = result.global_types)
    (hn : env.num_imported_globals = result.num_imported_globals)
    (ht : env.table_types = result.table_types) : ElementValid env entry := by
  obtain ⟨hm, hi⟩ := h
  constructor
  · cases hmode : entry.mode with
    | Passive | Declarative => trivial
    | Active index offset =>
      rw [hmode] at hm
      obtain ⟨hb, he, hv⟩ := hm
      exact ⟨by simpa [ht] using hb, by simpa [ht] using he, hv.same_caches hf hg hn⟩
  · intro value hv
    exact (hi value hv).same_caches hf hg hn

/-- The element loop adds `count` elements forming a `Rep` span, each `ElementValid`. -/
@[step]
theorem metadata.decode_element_section_loop.profile_spec (data : Slice U8) (env : metadata.Env)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hsize : env.elements.val.length ≤ start.val) (hrefs : env.declared_funcs.val.length ≤ start.val) :
    metadata.decode_element_section_loop data env count start 0#u32 ⦃ r => match r.1 with
      | .Ok next => ∃ added, added.length = count.val ∧ ElementsAdded env r.2 added ∧
          At (Rep (ElementEncodingFor)) data start (added.map ModuleEnv.rawElement) next ∧
          (∀ entry ∈ added, ElementValid env entry) ∧ r.2.elements.val.length ≤ next.val ∧
          r.2.declared_funcs.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  unfold metadata.decode_element_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ ∃ added, added.length = s.2.2.val ∧
      ElementsAdded env s.1 added ∧
      At (Rep (ElementEncodingFor)) data start (added.map ModuleEnv.rawElement) s.2.1 ∧
      (∀ entry ∈ added, ElementValid env entry) ∧ s.1.elements.val.length ≤ s.2.1.val ∧
      s.1.declared_funcs.val.length ≤ s.2.1.val)
  · rintro ⟨current, pos, i⟩ ⟨hi, added, hlen, henv, hbytes, hvalid, hsize, hrefs⟩
    dsimp only at hi hlen henv hbytes hvalid hsize hrefs
    unfold metadata.decode_element_section_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : i.val = count.val := by scalar_tac
      exact ⟨added, by omega, henv, hbytes, hvalid, hsize, hrefs⟩
    · rename_i hmore
      obtain ⟨⟨r, updated⟩, hr, hp⟩ := WP.spec_imp_exists
        (metadata.decode_element.spec data pos current hrefs)
      rw [hr]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
        obtain ⟨entry, next⟩ := pair
        obtain ⟨hb, hadded, hv, hbound, hprogress⟩ := hp
        dsimp only at hadded hbound
        have hspan := hb.span
        have hunchanged : updated.elements = current.elements := by rw [hadded.1]
        have hcapacity : updated.elements.val.length < Usize.max := by
          rw [hunchanged]
          scalar_tac
        have hentry : ElementValid env entry := by
          apply element_valid_caches hv <;> rw [henv.1]
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step as ⟨elements, helements⟩
        step
        refine ⟨?_, ⟨added ++ [entry], ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · scalar_tac
        · simp only [List.length_append, List.length_singleton]; scalar_tac
        · refine ⟨?_, ?_, ?_⟩
          · rw [hadded.1, henv.1]
          · simp only [helements, hunchanged, henv.2.1, List.append_assoc]
          · simp only [hadded.2, henv.2.2, List.flatMap_append, List.flatMap_cons,
              List.flatMap_nil, List.append_nil, List.append_assoc]
        · simpa only [List.map_append, List.map_cons, List.map_nil, ModuleEnv.rawElement]
            using hbytes.snoc hb
        · intro value hm
          rcases List.mem_append.mp hm with hm | hm
          · exact hvalid value hm
          · simpa [List.mem_singleton.mp hm] using hentry
        · simp only [helements, hunchanged, List.length_append, List.length_singleton]
          omega
        · exact hbound
        · scalar_tac
  · exact ⟨by simp, [], by simp, ⟨by cases env; rfl, by simp, by simp⟩,
      ⟨[], .nil, Wasm1.BytesAt.nil data start hstart⟩, by simp, hsize, hrefs⟩

/-- `metadata.decode_element_section` adds the elements of a `VecEncoding` span, each
`ElementValid`. -/
@[step]
theorem metadata.decode_element_section.profile_spec (data : Slice U8) (pos : Usize) (env : metadata.Env)
    (hsize : env.elements.val.length ≤ pos.val) (hrefs : env.declared_funcs.val.length ≤ pos.val) :
    metadata.decode_element_section data pos env ⦃ r => match r.1 with
      | .Ok next => ∃ added, ElementsAdded env r.2 added ∧
          At (VecEncoding (ElementEncodingFor)) data pos (added.map ModuleEnv.rawElement) next ∧
          (∀ entry ∈ added, ElementValid env entry) ∧ r.2.elements.val.length ≤ next.val ∧
          r.2.declared_funcs.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e => simp [metadata.decode_element_section, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    obtain ⟨count, start⟩ := pair
    have hs := hc.span
    obtain ⟨⟨r, result⟩, hloop, hp⟩ := WP.spec_imp_exists
      (metadata.decode_element_section_loop.profile_spec data env count start hs.2.2 (by omega) (by omega))
    simp [metadata.decode_element_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
    rw [hloop]
    cases r with
    | Err e => simp
    | Ok next =>
      obtain ⟨added, hlen, henv, hb, ht, hsize, hrefs⟩ := hp
      exact ⟨added, henv, At.vector hc hb (by simpa using hlen), ht, hsize, hrefs⟩

end Itasca

end

/-! ## Tail -/

section

/-!
# Module tail parser

The tail is the input after the code section: custom sections, at most one data section, then
custom sections, running to EOF. `ModuleTail.Encoding` is its independent grammar and `Prefix` the
invariant of the parsing loop. `metadata.validate_tail_with.spec` shows that an accepted tail is an
`Encoding` span to EOF whose segments are valid and agree with the data count, for any visitor
whose custom-section hook returns normally (`HooksTotal`). `metadata.validate_tail.spec` is the
specialization to the empty visitor. Completeness is in `Module/Sections/TailComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleTail

open ModuleBinary

/-- Custom section sequences concatenate. -/
theorem customs_append {xs ys} (hx : CustomsEncoding xs) (hy : CustomsEncoding ys) :
    CustomsEncoding (xs ++ ys) := by
  induction hx with
  | nil => simpa using hy
  | cons h _ ih => simpa [List.append_assoc] using CustomsEncoding.cons h ih

/-- The loop invariant: the bytes so far are custom sections plus at most one data section whose
segments are listed. The flag records whether the data section has occurred. -/
inductive Prefix :
    Bool → List ModuleBinary.Data → List U8 → Prop where
  | empty : Prefix false [] []
  | custom {seen segments before bytes} : Prefix seen segments before →
      CustomEncoding bytes → Prefix seen segments (before ++ bytes)
  | data {before bytes segments} : Prefix false [] before →
      SectionEncoding 11#u8 (VecEncoding (DataEncodingFor)) segments bytes →
      Prefix true segments (before ++ bytes)

/-- Before the data section, a prefix has no segments and is only custom sections. -/
theorem Prefix.not_seen {seen segments bytes} (h : Prefix seen segments bytes)
    (hs : seen = false) : segments = [] ∧ CustomsEncoding bytes := by
  induction h with
  | empty => exact ⟨rfl, .nil⟩
  | custom _ hc ih =>
    obtain ⟨he, hp⟩ := ih hs
    exact ⟨he, by simpa using customs_append hp (.cons hc .nil)⟩
  | data => cases hs

/-- The independent grammar of the tail: padded data section (custom sections, then an optional
data section) followed by custom sections. -/
def Encoding (segments : List ModuleBinary.Data) (bytes : List U8) : Prop :=
  ∃ chunk customs, PaddedEncoding 11#u8 (VecEncoding (DataEncodingFor)) [] segments chunk ∧
    CustomsEncoding customs ∧ bytes = chunk ++ customs

/-- A prefix is a tail encoding. -/
theorem Prefix.encoding {seen segments bytes} (h : Prefix seen segments bytes) :
    Encoding segments bytes := by
  induction h with
  | empty => exact ⟨[], [], ⟨[], [], .nil, .absent, rfl⟩, .nil, rfl⟩
  | custom _ hc ih =>
    obtain ⟨chunk, customs, hs, ht, he⟩ := ih
    exact ⟨chunk, _, hs, (by simpa using customs_append ht (.cons hc .nil)), by simp [he, List.append_assoc]⟩
  | data hp hd =>
    exact ⟨_, [], ⟨_, _, (hp.not_seen rfl).2, .present hd, rfl⟩, .nil, by simp⟩

/-- A section header and its payload span form a section encoding. -/
theorem header_payload {α : Type} {R : α → List U8 → Prop} {data start id first last value}
    (hh : SectionHeader data start id first last)
    (hp : At R data first value last) :
    At (SectionEncoding id R) data start value last := by
  obtain ⟨pos, size, hb, hd, he, hend⟩ := hh
  obtain ⟨payload, hp, hs⟩ := hp
  obtain ⟨sizeBytes, hd, hl, hn, hc⟩ := hd
  have hlen : payload.length = size.val := by have := hs.length; omega
  have hsize : Wasm1.BytesAt data pos sizeBytes first := ⟨hd, hl, hn⟩
  refine ⟨id :: (sizeBytes ++ payload), ⟨sizeBytes, payload, ?_, hp, rfl⟩, ?_⟩
  · simpa [hlen] using hc
  · simpa using hb.byte.append (hsize.append hs)

/-- A custom section header and a name within it form a `CustomEncoding` span. -/
theorem custom_encoded {data start first last nm} {custom : wasm_types.CustomSection}
    (hh : SectionHeader data start 0#u8 first last)
    (hn : At NameEncoding data first nm custom.payload_start)
    (hp : custom.payload_start.val ≤ last.val) :
    At (fun (_ : Unit) => CustomEncoding) data start () last := by
  obtain ⟨payload, _, hs⟩ := WP.spec_imp_exists
    (metadata.copy_bytes.spec data custom.payload_start last hp hh.span.2.2)
  obtain ⟨nameBytes, hn, hns⟩ := hn
  have hpayload : At (fun (_ : Unit) bs => bs = nameBytes ++ payload.val) data first () last :=
    ⟨nameBytes ++ payload.val, rfl, hns.append hs⟩
  obtain ⟨bytes, he, hb⟩ := header_payload hh hpayload
  exact ⟨bytes, ⟨nm, payload.val, nameBytes, hn, he⟩, hb⟩

/-- A custom section extends a tail prefix. -/
theorem append_custom {seen segments data start pos next}
    (hp : At (fun segments bytes => Prefix seen segments bytes) data start segments pos)
    (hc : At (fun (_ : Unit) => CustomEncoding) data pos () next) :
    At (fun segments bytes => Prefix seen segments bytes) data start segments next := by
  obtain ⟨before, hp, hs⟩ := hp
  obtain ⟨bytes, hc, ht⟩ := hc
  exact ⟨before ++ bytes, .custom hp hc, hs.append ht⟩

/-- A data section extends a prefix that has not seen one. -/
theorem append_data {old segments data start pos next}
    (hp : At (fun segments bytes => Prefix false segments bytes) data start old pos)
    (hd : At (SectionEncoding 11#u8 (VecEncoding (DataEncodingFor))) data pos segments next) :
    At (fun segments bytes => Prefix true segments bytes) data start segments next := by
  obtain ⟨before, hp, hs⟩ := hp
  obtain ⟨bytes, hd, ht⟩ := hd
  have he := (hp.not_seen rfl).1
  subst old
  exact ⟨before ++ bytes, .data hp hd, hs.append ht⟩

/-- The empty module visitor has total hooks. -/
theorem empty_hooks_total : HooksTotal metadata.EmptyModuleVisitor.Insts.ItascaMetadataModuleVisitor := by
  intro v chunk
  exact ⟨(.Ok (), v), rfl⟩

end Itasca.ModuleTail

namespace Itasca

/-- `metadata.validate_tail_with` consumes the input to EOF as custom sections around at most one data
section. An accepted tail is an `Encoding` span with valid segments that agree with the data
count. Hooks may reject. -/
theorem metadata.validate_tail_with.spec {V : Type} (visitor : metadata.ModuleVisitor V)
    (htotal : ModuleTail.HooksTotal visitor) (data : Slice U8) (start : Usize)
    (env : metadata.Env) (v : V) (hstart : start.val ≤ data.length) :
    metadata.validate_tail_with visitor data start env v ⦃ r => match r.1 with
      | .Ok tail => ModuleBinary.At (fun segments bytes => ModuleTail.Encoding segments bytes) data start
          (tail.data.val.map ModuleData.raw) (Slice.len data) ∧
          (∀ segment ∈ tail.data.val, ModuleData.Valid env segment) ∧
          ∀ count, env.data_count = some count → count.val = tail.data.val.length
      | .Err _ => True ⦄ := by
  unfold metadata.validate_tail_with metadata.validate_tail_with_loop
  apply loop.spec_decr_nat (fun s => data.length - s.2.2.1.val)
    (fun s => ModuleBinary.At (fun segments bytes => ModuleTail.Prefix s.2.2.2 segments bytes) data start
        (s.2.1.val.map ModuleData.raw) s.2.2.1 ∧
      ∀ segment ∈ s.2.1.val, ModuleData.Valid env segment)
  · rintro ⟨state, segments, pos, seen⟩ ⟨hbytes, hvalid⟩
    dsimp only at hbytes hvalid
    have hpos : pos.val ≤ data.length := hbytes.span.2
    unfold metadata.validate_tail_with_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : pos = Slice.len data := by apply UScalar.eq_of_val_eq; scalar_tac
      obtain ⟨bytes, hp, hs⟩ := hbytes
      cases hcount : env.data_count with
      | none =>
        simp only [WP.spec_ok]
        exact ⟨⟨bytes, hp.encoding, heq ▸ hs⟩, hvalid, by simp⟩
      | some count =>
        step
        split
        · simp
        · simp only [WP.spec_ok]
          refine ⟨⟨bytes, hp.encoding, heq ▸ hs⟩, hvalid, ?_⟩
          intro other ho
          have he : other = count := Option.some.inj ho.symm
          subst other
          scalar_tac
    · rename_i hmore
      have hlt : pos.val < data.length := by scalar_tac
      obtain ⟨r, hr, hh⟩ := WP.spec_imp_exists (metadata.read_section_header.spec data pos)
      rw [hr]
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok triple =>
        rcases triple with ⟨id, first, last⟩
        change ModuleBinary.SectionHeader data pos id first last at hh
        have hspan := hh.span
        simp [core.result.Result.Insts.CoreOpsTry.branch]
        by_cases hc : id = metadata.SECTION_CUSTOM
        · simp only [hc, ↓reduceIte]
          obtain ⟨r, hcustom, hp⟩ := WP.spec_imp_exists (metadata.decode_custom_section.spec data first last)
          rw [hcustom]
          cases r with
          | Err e =>
            simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok custom =>
            obtain ⟨nm, hn, hbefore, hend, _⟩ := hp
            have hb := ModuleTail.custom_encoded (by simpa [hc, metadata.SECTION_CUSTOM] using hh) hn hbefore
            obtain ⟨⟨res, state'⟩, hvisit⟩ := htotal state custom
            simp [hvisit]
            cases res with
            | Err e => simp
            | Ok u =>
              exact ⟨ModuleTail.append_custom hbytes hb, hvalid, by scalar_tac⟩
        · simp only [hc, ↓reduceIte]
          by_cases hd : id = metadata.SECTION_DATA
          · subst id
            simp only [↓reduceIte]
            cases seen with
            | true => simp
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              obtain ⟨r, hdata, hp⟩ := WP.spec_imp_exists (metadata.decode_data_section.profile_spec data first env)
              rw [hdata]
              cases r with
              | Err e =>
                simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
              | Ok pair =>
                rcases pair with ⟨decoded, next⟩
                obtain ⟨hencoded, htyped⟩ := hp
                simp
                by_cases he : next = last
                · subst next
                  simp only [↓reduceIte, WP.spec_ok]
                  have hb := ModuleTail.header_payload hh hencoded
                  exact ⟨ModuleTail.append_data hbytes (by simpa [metadata.SECTION_DATA] using hb), htyped, by scalar_tac⟩
                · have hn : next.val ≠ last.val := fun h => he (UScalar.eq_of_val_eq h)
                  simp [hn]
          · have hn : id.val ≠ metadata.SECTION_DATA.val := fun h => hd (UScalar.eq_of_val_eq h)
            simp [hn]
  · refine ⟨?_, by simp [alloc.vec.Vec.new]⟩
    exact ⟨[], .empty, Wasm1.BytesAt.nil data start hstart⟩

/-- `metadata.validate_tail` satisfies the same specification as `metadata.validate_tail_with`. -/
theorem metadata.validate_tail.spec (data : Slice U8) (start : Usize) (env : metadata.Env)
    (hstart : start.val ≤ data.length) :
    metadata.validate_tail data start env ⦃ r => match r with
      | .Ok tail => ModuleBinary.At (fun segments bytes => ModuleTail.Encoding segments bytes) data start
          (tail.data.val.map ModuleData.raw) (Slice.len data) ∧
          (∀ segment ∈ tail.data.val, ModuleData.Valid env segment) ∧
          ∀ count, env.data_count = some count → count.val = tail.data.val.length
      | .Err _ => True ⦄ := by
  obtain ⟨⟨r, state⟩, hr, hp⟩ := WP.spec_imp_exists
    (metadata.validate_tail_with.spec metadata.EmptyModuleVisitor.Insts.ItascaMetadataModuleVisitor
      ModuleTail.empty_hooks_total data start env () hstart)
  simpa [metadata.validate_tail, hr] using hp

end Itasca

end
