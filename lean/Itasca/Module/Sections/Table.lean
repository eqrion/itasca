import Itasca.Module.Sections.Type

/-!
# Table section parser

Soundness of `metadata.decode_table_section` and its loop. `TablesAdded` says the environment gains
the decoded table types. The span is a `VecEncoding TableTypeEncoding`, each table has limits
within the table cap. Completeness is in `Module/Sections/TableComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- A table type encoding consumes at least one byte. -/
theorem At.tableType_progress {data start ty next} (h : At TableTypeEncoding data start ty next) :
    start.val < next.val := by
  obtain ⟨bytes, he, hs⟩ := h
  obtain ⟨limits, _, rfl⟩ := he
  have := hs.length
  simp only [List.length_cons] at this
  omega

end Itasca.ModuleBinary

namespace Itasca.ModuleSections

/-- `result` is `env` with the table types `added` appended and nothing else changed. -/
def TablesAdded (env result : metadata.Env) (added : List wasm_types.TableType) : Prop :=
  result = { env with table_types := result.table_types } ∧ result.table_types.val = env.table_types.val ++ added

end Itasca.ModuleSections

namespace Itasca

open ModuleBinary ModuleSections

/-- The table loop adds `count` table types forming a `Rep TableTypeEncoding` span, with valid
limits. -/
@[step]
theorem metadata.decode_table_section_loop.spec (data : Slice U8) (env : metadata.Env)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hsize : env.table_types.val.length ≤ start.val) :
    metadata.decode_table_section_loop data env count start 0#u32 ⦃ r => match r.1 with
      | .Ok next => ∃ added, added.length = count.val ∧ TablesAdded env r.2 added ∧
          At (Rep TableTypeEncoding) data start added next ∧
          (∀ ft ∈ added, ModuleTranslation.LimitsValid ft.limits (2 ^ 32 - 1)) ∧ r.2.table_types.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  unfold metadata.decode_table_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ ∃ added, added.length = s.2.2.val ∧
      TablesAdded env s.1 added ∧ At (Rep TableTypeEncoding) data start added s.2.1 ∧
      (∀ ft ∈ added, ModuleTranslation.LimitsValid ft.limits (2 ^ 32 - 1)) ∧ s.1.table_types.val.length ≤ s.2.1.val)
  · rintro ⟨current, pos, i⟩ ⟨hi, added, hlen, henv, hbytes, hvalid, hsize⟩
    dsimp only at hi hlen henv hbytes hvalid hsize
    unfold metadata.decode_table_section_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : i.val = count.val := by scalar_tac
      exact ⟨added, by omega, henv, hbytes, hvalid, hsize⟩
    · rename_i hmore
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (metadata.decode_table_type.spec data pos)
      rw [hr]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
        obtain ⟨ft, next⟩ := pair
        obtain ⟨hb, ht⟩ := hp
        have hprogress := hb.tableType_progress
        have hbound := hb.span.2
        have hcapacity : current.table_types.val.length < Usize.max := by scalar_tac
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step
        step
        refine ⟨?_, ⟨added ++ [ft], ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
        · scalar_tac
  · exact ⟨by simp, [], by simp, ⟨by cases env; rfl, by simp⟩,
      ⟨[], .nil, Wasm1.BytesAt.nil data start hstart⟩, by simp, hsize⟩

/-- `metadata.decode_table_section` adds the table types of a `VecEncoding TableTypeEncoding` span,
with valid limits. -/
@[step]
theorem metadata.decode_table_section.spec (data : Slice U8) (pos : Usize) (env : metadata.Env)
    (hsize : env.table_types.val.length ≤ pos.val) :
    metadata.decode_table_section data pos env ⦃ r => match r.1 with
      | .Ok next => ∃ added, TablesAdded env r.2 added ∧
          At (VecEncoding TableTypeEncoding) data pos added next ∧
          (∀ ft ∈ added, ModuleTranslation.LimitsValid ft.limits (2 ^ 32 - 1)) ∧ r.2.table_types.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e => simp [metadata.decode_table_section, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    obtain ⟨count, start⟩ := pair
    have hs := hc.span
    obtain ⟨⟨r, result⟩, hloop, hp⟩ := WP.spec_imp_exists
      (metadata.decode_table_section_loop.spec data env count start hs.2.2 (by omega))
    simp [metadata.decode_table_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
    rw [hloop]
    cases r with
    | Err e => simp
    | Ok next =>
      obtain ⟨added, hlen, henv, hb, ht, hsize⟩ := hp
      exact ⟨added, henv, At.vector hc hb hlen, ht, hsize⟩

end Itasca
