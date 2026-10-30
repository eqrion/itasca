import Itasca.Module.Env.Basic
import Itasca.Module.Readers.Types

/-!
# Type section parser

Soundness of `metadata.decode_type_section` and its loop. `TypesAdded` says the environment gains
exactly the decoded signatures. The `profile_spec` forms give a `VecEncoding FuncTypeEncoding`
span whose signatures satisfy the profile restrictions, caps and allowed value types, and the
Wasm 1.0 forms give the single-result bound. `metadata.check_table_count` enforces the Wasm 1.0
limit of one table. Completeness is in `Module/Sections/TypeComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- A repetition span extends by one element at its end. -/
theorem At.snoc {α : Type} {R : α → List U8 → Prop} {data start pos next values value}
    (h : At (Rep R) data start values pos) (h' : At R data pos value next) :
    At (Rep R) data start (values ++ [value]) next := by
  obtain ⟨bytes, hr, hs⟩ := h
  obtain ⟨last, he, ht⟩ := h'
  exact ⟨bytes ++ last, hr.snoc he, hs.append ht⟩

/-- A decoded count, a repetition of that many elements and their span form a `VecEncoding`. -/
theorem At.vector {α : Type} {R : α → List U8 → Prop} {data start pos next count values}
    (hc : Leb128.Decoded data start count pos)
    (he : At (Rep R) data pos values next) (hlen : values.length = count.val) :
    At (VecEncoding R) data start values next := by
  obtain ⟨bytes, hr, hs⟩ := he
  obtain ⟨countBytes, hcs, hcl, hcb, hce⟩ := hc
  exact ⟨countBytes ++ bytes,
    ⟨countBytes, bytes, by simpa [hlen] using hce, hr, rfl⟩,
    (show Wasm1.BytesAt data start countBytes pos from ⟨hcs, hcl, hcb⟩).append hs⟩

/-- A function type encoding consumes at least one byte. -/
theorem At.funcType_progress {data start ty next} (h : At FuncTypeEncoding data start ty next) :
    start.val < next.val := by
  obtain ⟨bytes, ⟨params, results, _, _, rfl⟩, hs⟩ := h
  have := hs.length
  simp only [List.length_cons, List.length_append] at this
  omega

end Itasca.ModuleBinary

namespace Itasca.ModuleSections

/-- `result` is `env` with the signatures `added` appended to its type table and nothing else
changed. -/
def TypesAdded (env result : metadata.Env) (added : List wasm_types.FuncType) : Prop :=
  result = { env with types := result.types } ∧ result.types.val = env.types.val ++ added

end Itasca.ModuleSections

namespace Itasca

open ModuleBinary ModuleSections

/-- `metadata.check_table_count` rejects exactly when the profile is Wasm 1.0 and there is more than
one table. -/
@[step]
theorem metadata.check_table_count.spec (env : metadata.Env) (profile : ValidationProfile) :
    metadata.check_table_count env profile ⦃ result => match result with
      | .Ok _ => profile = .Wasm1 → env.table_types.val.length ≤ 1
      | .Err _ => profile = .Wasm1 ∧ 1 < env.table_types.val.length ⦄ := by
  cases profile with
  | Wasm2 => simp [metadata.check_table_count]
  | Wasm1 =>
    simp only [metadata.check_table_count]
    split <;> simp_all [global_simps]

/-- `metadata.check_table_count` accepts when the Wasm 1.0 table limit holds. -/
theorem metadata.check_table_count.complete (env : metadata.Env) (profile : ValidationProfile)
    (h : profile = .Wasm1 → env.table_types.val.length ≤ 1) :
    metadata.check_table_count env profile = .ok (.Ok ()) := by
  cases profile with
  | Wasm2 => simp [metadata.check_table_count]
  | Wasm1 =>
    have hb := h rfl
    simp [metadata.check_table_count, limits.MAX_TABLES, global_simps, show ¬1 < env.table_types.val.length by omega]

/-- The type loop adds `count` signatures forming a `Rep FuncTypeEncoding` span. Each satisfies the
profile restrictions, caps and allowed value types. -/
@[step]
theorem metadata.decode_type_section_loop.profile_spec (data : Slice U8) (env : metadata.Env)
    (profile : ValidationProfile) (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hsize : env.types.val.length ≤ start.val) :
    metadata.decode_type_section_loop data env profile count start 0#u32 ⦃ r => match r.1 with
      | .Ok next => ∃ added, added.length = count.val ∧ TypesAdded env r.2 added ∧
          At (Rep FuncTypeEncoding) data start added next ∧
          (∀ ft ∈ added, (Profile.FuncType profile ft ∧ Profile.FuncTypeWithinLimits ft) ∧
            ∀ ty ∈ ft.params.val ++ ft.results.val, ValueTypeAllowed profile ty) ∧ r.2.types.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  unfold metadata.decode_type_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ ∃ added, added.length = s.2.2.val ∧
      TypesAdded env s.1 added ∧ At (Rep FuncTypeEncoding) data start added s.2.1 ∧
      (∀ ft ∈ added, (Profile.FuncType profile ft ∧ Profile.FuncTypeWithinLimits ft) ∧
            ∀ ty ∈ ft.params.val ++ ft.results.val, ValueTypeAllowed profile ty) ∧ s.1.types.val.length ≤ s.2.1.val)
  · rintro ⟨current, pos, i⟩ ⟨hi, added, hlen, henv, hbytes, hvalid, hsize⟩
    dsimp only at hi hlen henv hbytes hvalid hsize
    unfold metadata.decode_type_section_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : i.val = count.val := by scalar_tac
      exact ⟨added, by omega, henv, hbytes, hvalid, hsize⟩
    · rename_i hmore
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (metadata.decode_func_type.allowed_spec data pos profile)
      rw [hr]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
        obtain ⟨ft, next⟩ := pair
        obtain ⟨⟨hb, ht⟩, ha⟩ := hp
        have hprogress := hb.funcType_progress
        have hbound := hb.span.2
        have hcapacity : current.types.val.length < Usize.max := by scalar_tac
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
          · exact ⟨(hvalid ty hm).1.1, (hvalid ty hm).1.2, (hvalid ty hm).2⟩
          · simpa [List.mem_singleton.mp hm] using And.intro ht ha
        · simp only [r_post, List.length_append, List.length_singleton]; omega
        · scalar_tac
  · exact ⟨by simp, [], by simp, ⟨by cases env; rfl, by simp⟩,
      ⟨[], .nil, Wasm1.BytesAt.nil data start hstart⟩, by simp, hsize⟩

/-- `metadata.decode_type_section` adds the signatures of a `VecEncoding FuncTypeEncoding` span, each
satisfying the profile restrictions, caps and allowed value types. -/
@[step]
theorem metadata.decode_type_section.profile_spec (data : Slice U8) (pos : Usize) (env : metadata.Env)
    (profile : ValidationProfile) (hsize : env.types.val.length ≤ pos.val) :
    metadata.decode_type_section data pos env profile ⦃ r => match r.1 with
      | .Ok next => ∃ added, TypesAdded env r.2 added ∧
          At (VecEncoding FuncTypeEncoding) data pos added next ∧
          (∀ ft ∈ added, (Profile.FuncType profile ft ∧ Profile.FuncTypeWithinLimits ft) ∧
            ∀ ty ∈ ft.params.val ++ ft.results.val, ValueTypeAllowed profile ty) ∧ r.2.types.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e => simp [metadata.decode_type_section, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    obtain ⟨count, start⟩ := pair
    have hs := hc.span
    obtain ⟨⟨r, result⟩, hloop, hp⟩ := WP.spec_imp_exists
      (metadata.decode_type_section_loop.profile_spec data env profile count start hs.2.2 (by omega))
    simp [metadata.decode_type_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
    rw [hloop]
    cases r with
    | Err e => simp
    | Ok next =>
      obtain ⟨added, hlen, henv, hb, ht, hsize⟩ := hp
      exact ⟨added, henv, At.vector hc hb hlen, by simpa only [and_assoc, List.mem_append] using ht, hsize⟩

end Itasca
