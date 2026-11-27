import Itasca.Module.Sections.Headers
import Itasca.Module.Readers.Completeness

/-! ## Import -/

section

/-!
# Single import parser

Soundness of `metadata.decode_import`. `ImportAdded` says that the environment gains the import
and updates only the index space of its kind, with the limits and memory count checks of
that kind. The decoded bytes are an `ImportEncoding` span and the environment stays `Bounded`.
Completeness is in `Module/Sections/IndexSpacesComplete`.
-/

set_option maxHeartbeats 800000

open Aeneas Aeneas.Std

namespace Itasca.Module.Sections

/-- `result` is `env` with `entry` appended to the imports and to the index space of its kind.
Functions must resolve their type, tables and memories satisfy their limits, and memories
respect the count cap. -/
def ImportAdded (env result : metadata.ModuleMetadata metadata.CodeMetadata) (entry : Binary.Import) : Prop :=
  (∃ actual, result.imports.val = env.imports.val ++ [actual] ∧
    (actual.module.val, actual.name.val, actual.kind) = Module.Environment.importRecord entry) ∧
  match entry.desc with
  | .Func idx =>
      idx.val < env.code.types.val.length ∧
      result = { env with imports := result.imports, code := { env.code with
        funcs := result.code.funcs, num_imported_funcs := result.code.num_imported_funcs } } ∧
      result.code.funcs.val = env.code.funcs.val ++ [⟨idx,false,false⟩] ∧
      result.code.num_imported_funcs.val = env.code.num_imported_funcs.val + 1
  | .Global gt =>
      result = { env with imports := result.imports, code := { env.code with
        globals := result.code.globals, num_imported_globals := result.code.num_imported_globals } } ∧
      result.code.globals.val = env.code.globals.val ++ [⟨gt,none,false⟩] ∧
      result.code.num_imported_globals.val = env.code.num_imported_globals.val + 1
  | .Table tt =>
      result = { env with imports := result.imports, code := { env.code with tables := result.code.tables } } ∧
      result.code.tables.val = env.code.tables.val ++ [⟨tt,true,false⟩] ∧
      Module.Translation.LimitsValid tt.limits (2 ^ 32 - 1)
  | .Memory mt =>
      result = { env with imports := result.imports, code := { env.code with memories := result.code.memories } } ∧
      result.code.memories.val = env.code.memories.val ++ [⟨mt,true,false⟩] ∧ result.code.memories.val.length ≤ 1 ∧
      Module.Translation.LimitsValid mt.limits (2 ^ 16)

/-- A module name, an import name and a descriptor span in sequence form an `ImportEncoding`. -/
theorem import_encoded {data start p1 p2 next moduleName nm desc}
    (hm : Binary.At Binary.NameEncoding data start moduleName p1)
    (hn : Binary.At Binary.NameEncoding data p1 nm p2)
    (hd : Binary.At Binary.ImportDescEncoding data p2 desc next) :
    Binary.At Binary.ImportEncoding data start ⟨moduleName, nm, desc⟩ next := by
  obtain ⟨mb, hm, hs⟩ := hm
  obtain ⟨nb, hn, hns⟩ := hn
  obtain ⟨db, hd, hds⟩ := hd
  exact ⟨mb ++ nb ++ db, Binary.ImportEncoding.reader_parts.mpr ⟨mb, nb, db, hm, hn, hd, rfl⟩, (hs.append hns).append hds⟩

end Itasca.Module.Sections

namespace Itasca

open Binary Module.Sections

/-- `metadata.decode_import` adds one import to the environment (`ImportAdded`), the bytes are its
`ImportEncoding` span, and the environment stays within the byte bound. -/
@[step]
theorem metadata.decode_import.spec (data : Slice U8) (pos : Usize) (env : (metadata.ModuleMetadata metadata.CodeMetadata))
    (hbound : Module.Environment.Bounded env pos.val) :
    metadata.decode_import data pos env ⦃ r => match r.1 with
      | .Ok next => ∃ entry, ImportAdded env r.2 entry ∧
          At ImportEncoding data pos entry next ∧
          Module.Environment.Bounded r.2 next.val
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
            by_cases hlookup : value.val < env.code.types.val.length
            · have hcapacity : env.code.funcs.val.length < Usize.max := by scalar_tac
              have hcapacityI : env.imports.val.length < Usize.max := by scalar_tac
              have hcapacityN : env.code.num_imported_funcs.val < Usize.max := by scalar_tac
              simp [hd, lift, Nat.not_le_of_gt hlookup]
              step as ⟨funcs,v_post⟩
              step as ⟨n,i_post⟩
              step as ⟨imports,v1_post⟩
              let entry : Binary.Import := ⟨modname.val, nm.val, .Func value⟩
              refine ⟨entry, ?_, ?_, ?_⟩
              · refine ⟨⟨_,v1_post,rfl⟩, hlookup, rfl, v_post, i_post⟩
              · apply import_encoded hm hname
                apply At.prepend (by with_unfolding_all exact hkind) (At.of_u32 hdesc)
                intro bytes hbytes
                exact .func value.val ((Leb128.encoding_iff _ _).mp hbytes)
              · constructor <;> simp only [v_post, v1_post, List.length_append, List.length_singleton] <;> scalar_tac
            · simp [hd, lift, Nat.le_of_not_gt hlookup]
        · obtain ⟨r, hd, hdesc⟩ := WP.spec_imp_exists (metadata.decode_table_type.spec data p3)
          cases r with
          | Err e => simp [hd,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok pair =>
            obtain ⟨value, next⟩ := pair
            obtain ⟨hdesc, hlimits⟩ := hdesc
            have hspanD := hdesc.span
            have hcapacity : env.code.tables.val.length < Usize.max := by scalar_tac
            have hcapacityI : env.imports.val.length < Usize.max := by scalar_tac
            simp [hd]
            step
            step
            let entry : Binary.Import := ⟨modname.val, nm.val, .Table value⟩
            refine ⟨entry, ?_, ?_, ?_⟩
            · refine ⟨⟨_,v1_post,rfl⟩, rfl, v_post, ?_⟩
              simpa [Module.Translation.LimitsValid, Binary.LimitsValid, Option.mem_def, global_simps, U32.rMax] using hlimits
            · apply import_encoded hm hname
              apply At.prepend (by with_unfolding_all exact hkind) hdesc
              intro bytes hbytes
              exact .table _ hbytes
            · constructor <;> simp only [v_post, v1_post, List.length_append, List.length_singleton] <;> scalar_tac
        · obtain ⟨r, hd, hdesc⟩ := WP.spec_imp_exists (metadata.decode_mem_type.spec data p3)
          cases r with
          | Err e => simp [hd,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok pair =>
            obtain ⟨value, next⟩ := pair
            obtain ⟨hdesc, hlimits⟩ := hdesc
            have hspanD := hdesc.span
            have hcapacity : env.code.memories.val.length < Usize.max := by scalar_tac
            have hcapacityI : env.imports.val.length < Usize.max := by scalar_tac
            simp [hd]
            step
            split
            · simp
            · rename_i hcount
              step
              let entry : Binary.Import := ⟨modname.val, nm.val, .Memory value⟩
              refine ⟨entry, ?_, ?_, ?_⟩
              · refine ⟨⟨_,v1_post,rfl⟩, rfl, v_post, ?_, ?_⟩
                · simpa [global_simps] using hcount
                · simpa [Module.Translation.LimitsValid, Binary.LimitsValid, Option.mem_def, global_simps, U32.rMax] using hlimits
              · apply import_encoded hm hname
                apply At.prepend (by with_unfolding_all exact hkind) hdesc
                intro bytes hbytes
                exact .memory _ hbytes
              · constructor <;> simp only [v_post, v1_post, List.length_append, List.length_singleton] <;> scalar_tac
        · obtain ⟨r, hd, hdesc⟩ := WP.spec_imp_exists (metadata.decode_global_type.spec data p3)
          cases r with
          | Err e => simp [hd,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok pair =>
            obtain ⟨value, next⟩ := pair
            have hspanD := hdesc.span
            have hcapacity : env.code.globals.val.length < Usize.max := by scalar_tac
            have hcapacityI : env.imports.val.length < Usize.max := by scalar_tac
            have hcapacityN : env.code.num_imported_globals.val < Usize.max := by scalar_tac
            simp [hd]
            step
            step
            step
            let entry : Binary.Import := ⟨modname.val, nm.val, .Global value⟩
            refine ⟨entry, ?_, ?_, ?_⟩
            · exact ⟨⟨_,v1_post,rfl⟩, rfl, v_post, i_post⟩
            · apply import_encoded hm hname
              apply At.prepend (by with_unfolding_all exact hkind) hdesc
              intro bytes hbytes
              exact .global _ hbytes
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
`Module/Sections/IndexSpacesComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Sections

/-- `result` is `initial` after adding `entries` one at a time by `ImportAdded`. -/
inductive ImportsAdded (initial : (metadata.ModuleMetadata metadata.CodeMetadata)) : List Binary.Import → (metadata.ModuleMetadata metadata.CodeMetadata) →
    Prop where
  | nil : ImportsAdded initial [] initial
  | snoc {entries before after entry} : ImportsAdded initial entries before →
      ImportAdded before after entry → ImportsAdded initial (entries ++ [entry]) after

end Itasca.Module.Sections

namespace Itasca

open Binary Module.Sections

/-- The import loop adds `count` imports forming a `Rep ImportEncoding` span. -/
@[step]
theorem metadata.decode_import_section_loop.spec (data : Slice U8) (env : (metadata.ModuleMetadata metadata.CodeMetadata))
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hbound : Module.Environment.Bounded env start.val) :
    metadata.decode_import_section_loop data env count start 0#u32 ⦃ r => match r.1 with
      | .Ok next => ∃ entries, entries.length = count.val ∧ ImportsAdded env entries r.2 ∧
          At (Rep ImportEncoding) data start entries next ∧
          Module.Environment.Bounded r.2 next.val
      | .Err _ => True ⦄ := by
  unfold metadata.decode_import_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ ∃ entries, entries.length = s.2.2.val ∧
      ImportsAdded env entries s.1 ∧
      At (Rep ImportEncoding) data start entries s.2.1 ∧
      Module.Environment.Bounded s.1 s.2.1.val)
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
      ⟨[], .nil, Body.Scalar.BytesAt.nil data start hstart⟩, hbound⟩

/-- `metadata.decode_import_section` adds the imports of a `VecEncoding ImportEncoding` span. -/
@[step]
theorem metadata.decode_import_section.spec (data : Slice U8) (pos : Usize) (env : (metadata.ModuleMetadata metadata.CodeMetadata))
    (hbound : Module.Environment.Bounded env pos.val) :
    metadata.decode_import_section data pos env ⦃ r => match r.1 with
      | .Ok next => ∃ entries, ImportsAdded env entries r.2 ∧
          At (VecEncoding ImportEncoding) data pos entries next ∧
          Module.Environment.Bounded r.2 next.val
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
