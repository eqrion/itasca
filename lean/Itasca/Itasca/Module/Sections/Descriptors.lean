import Itasca.Module.Sections.Headers

/-! ## Memory -/

section

/-!
# Memory section parser

Soundness of `metadata.decode_memory_section` and its loop. `MemoriesAdded` says the environment
gains the decoded memory types. The span is a `VecEncoding MemTypeEncoding` whose limits are
within 2^16 pages, and the environment never holds more than one memory unless it already did.
Completeness is in `Module/Sections/IndexSpacesComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Binary

/-- A memory type encoding consumes at least one byte. -/
theorem At.mem_type_progress {data start ty next} (h : At MemTypeEncoding data start ty next) :
    start.val < next.val := by
  obtain ⟨bytes, he, hs⟩ := h
  change LimitsEncoding ty.limits bytes at he
  have hn : bytes ≠ [] := by
    rintro rfl
    exact WebAssembly.Binary.LimitsEncoding.nonempty he rfl
  have := hs.length
  have := List.length_pos_iff.mpr hn
  omega

end Itasca.Binary

namespace Itasca.Module.Sections

/-- `result` is `env` with the memory types `added` appended and nothing else changed. -/
def MemoriesAdded (env result : metadata.CodeMetadata) (added : List wasm_types.MemType) : Prop :=
  result = { env with memories := result.memories } ∧ result.memories.val = env.memories.val ++ added.map (fun ty => ⟨ty, false, false⟩)

end Itasca.Module.Sections

namespace Itasca

open Binary Module.Sections

/-- The memory loop adds `count` memory types forming a `Rep MemTypeEncoding` span with valid
limits. -/
@[step]
theorem metadata.decode_memory_section_loop.spec (data : Slice U8) (env : metadata.CodeMetadata)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hsize : env.memories.val.length ≤ start.val) :
    metadata.decode_memory_section_loop data env count start 0#u32 ⦃ r => match r.1 with
      | .Ok next => ∃ added, added.length = count.val ∧ MemoriesAdded env r.2 added ∧
          At (Rep MemTypeEncoding) data start added next ∧
          (∀ ft ∈ added, Module.Translation.LimitsValid ft.limits (2 ^ 16)) ∧ r.2.memories.val.length ≤ next.val ∧
          r.2.memories.val.length ≤ max env.memories.val.length 1
      | .Err _ => True ⦄ := by
  unfold metadata.decode_memory_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ ∃ added, added.length = s.2.2.val ∧
      MemoriesAdded env s.1 added ∧ At (Rep MemTypeEncoding) data start added s.2.1 ∧
      (∀ ft ∈ added, Module.Translation.LimitsValid ft.limits (2 ^ 16)) ∧ s.1.memories.val.length ≤ s.2.1.val ∧
      s.1.memories.val.length ≤ max env.memories.val.length 1)
  · rintro ⟨current, pos, i⟩ ⟨hi, added, hlen, henv, hbytes, hvalid, hsize, hcount⟩
    dsimp only at hi hlen henv hbytes hvalid hsize hcount
    unfold metadata.decode_memory_section_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : i.val = count.val := by scalar_tac
      exact ⟨added, by omega, henv, hbytes, hvalid, hsize, hcount⟩
    · rename_i hmore
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (metadata.decode_mem_type.spec data pos)
      rw [hr]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
        obtain ⟨ft, next⟩ := pair
        obtain ⟨hb, ht⟩ := hp
        have hprogress := hb.mem_type_progress
        have hbound := hb.span.2
        have hcapacity : current.memories.val.length < Usize.max := by scalar_tac
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step
        split
        · simp
        · rename_i hmax
          step
          refine ⟨?_, ⟨added ++ [ft], ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
          · scalar_tac
          · simp only [List.length_append, List.length_singleton]; scalar_tac
          · constructor
            · rw [henv.1]
            · simp [r_post, henv.2, List.append_assoc]
          · exact hbytes.snoc hb
          · intro ty hm
            rcases List.mem_append.mp hm with hm | hm
            · exact hvalid ty hm
            · simpa [List.mem_singleton.mp hm, Module.Translation.LimitsValid, Binary.LimitsValid,
                Option.mem_def, global_simps, U32.rMax] using ht
          · simp only [r_post, List.length_append, List.length_singleton]; omega
          · have hx : r.val.length ≤ 1 := by simpa [global_simps] using hmax
            exact hx.trans (Nat.le_max_right _ _)
          · scalar_tac
  · exact ⟨by simp, [], by simp, ⟨by cases env; rfl, by simp⟩,
      ⟨[], .nil, Body.Scalar.BytesAt.nil data start hstart⟩, by simp, hsize, Nat.le_max_left _ _⟩

/-- `metadata.decode_memory_section` adds the memory types of a `VecEncoding MemTypeEncoding` span
with valid limits. -/
@[step]
theorem metadata.decode_memory_section.spec (data : Slice U8) (pos : Usize) (env : metadata.CodeMetadata)
    (hsize : env.memories.val.length ≤ pos.val) :
    metadata.decode_memory_section data pos env ⦃ r => match r.1 with
      | .Ok next => ∃ added, MemoriesAdded env r.2 added ∧
          At (VecEncoding MemTypeEncoding) data pos added next ∧
          (∀ ft ∈ added, Module.Translation.LimitsValid ft.limits (2 ^ 16)) ∧ r.2.memories.val.length ≤ next.val ∧
          r.2.memories.val.length ≤ max env.memories.val.length 1
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e => simp [metadata.decode_memory_section, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    obtain ⟨count, start⟩ := pair
    have hs := hc.span
    obtain ⟨⟨r, result⟩, hloop, hp⟩ := WP.spec_imp_exists
      (metadata.decode_memory_section_loop.spec data env count start hs.2.2 (by omega))
    simp [metadata.decode_memory_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
    rw [hloop]
    cases r with
    | Err e => simp
    | Ok next =>
      obtain ⟨added, hlen, henv, hb, ht, hsize, hcount⟩ := hp
      exact ⟨added, henv, At.vector hc hb hlen, ht, hsize, by simpa using hcount⟩

end Itasca

end

/-! ## Table -/

section

/-!
# Table section parser

Soundness of `metadata.decode_table_section` and its loop. `TablesAdded` says the environment gains
the decoded table types. The span is a `VecEncoding TableTypeEncoding`, each table has limits
within the table cap. Completeness is in `Module/Sections/IndexSpacesComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Binary

/-- A table type encoding consumes at least one byte. -/
theorem At.table_type_progress {data start ty next} (h : At TableTypeEncoding data start ty next) :
    start.val < next.val := by
  obtain ⟨bytes, he, hs⟩ := h
  obtain ⟨limits, _, rfl⟩ := tableType_reader_span he
  have := hs.length
  simp only [List.length_cons] at this
  omega

end Itasca.Binary

namespace Itasca.Module.Sections

/-- `result` is `env` with the table types `added` appended and nothing else changed. -/
def TablesAdded (env result : metadata.CodeMetadata) (added : List wasm_types.TableType) : Prop :=
  result = { env with tables := result.tables } ∧ result.tables.val = env.tables.val ++ added.map (fun ty => ⟨ty, false, false⟩)

end Itasca.Module.Sections

namespace Itasca

open Binary Module.Sections

/-- The table loop adds `count` table types forming a `Rep TableTypeEncoding` span, with valid
limits. -/
@[step]
theorem metadata.decode_table_section_loop.spec (data : Slice U8) (env : metadata.CodeMetadata)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hsize : env.tables.val.length ≤ start.val) :
    metadata.decode_table_section_loop data env count start 0#u32 ⦃ r => match r.1 with
      | .Ok next => ∃ added, added.length = count.val ∧ TablesAdded env r.2 added ∧
          At (Rep TableTypeEncoding) data start added next ∧
          (∀ ft ∈ added, Module.Translation.LimitsValid ft.limits (2 ^ 32 - 1)) ∧ r.2.tables.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  unfold metadata.decode_table_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ ∃ added, added.length = s.2.2.val ∧
      TablesAdded env s.1 added ∧ At (Rep TableTypeEncoding) data start added s.2.1 ∧
      (∀ ft ∈ added, Module.Translation.LimitsValid ft.limits (2 ^ 32 - 1)) ∧ s.1.tables.val.length ≤ s.2.1.val)
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
        have hprogress := hb.table_type_progress
        have hbound := hb.span.2
        have hcapacity : current.tables.val.length < Usize.max := by scalar_tac
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
          · simpa [List.mem_singleton.mp hm, Module.Translation.LimitsValid, Binary.LimitsValid,
              Option.mem_def, global_simps, U32.rMax] using ht
        · simp only [r_post, List.length_append, List.length_singleton]; omega
        · scalar_tac
  · exact ⟨by simp, [], by simp, ⟨by cases env; rfl, by simp⟩,
      ⟨[], .nil, Body.Scalar.BytesAt.nil data start hstart⟩, by simp, hsize⟩

/-- `metadata.decode_table_section` adds the table types of a `VecEncoding TableTypeEncoding` span,
with valid limits. -/
@[step]
theorem metadata.decode_table_section.spec (data : Slice U8) (pos : Usize) (env : metadata.CodeMetadata)
    (hsize : env.tables.val.length ≤ pos.val) :
    metadata.decode_table_section data pos env ⦃ r => match r.1 with
      | .Ok next => ∃ added, TablesAdded env r.2 added ∧
          At (VecEncoding TableTypeEncoding) data pos added next ∧
          (∀ ft ∈ added, Module.Translation.LimitsValid ft.limits (2 ^ 32 - 1)) ∧ r.2.tables.val.length ≤ next.val
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

end

/-! ## Function -/

section

/-!
# Function section parser

Soundness of `metadata.decode_function_section` and its loop. `FunctionsAdded` says the environment
gains the decoded type indices and the signatures they resolve to, in order. The decoded span is
a `VecEncoding IndexEncoding`. Completeness is in `Module/Sections/DeclarationsComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Sections

/-- Defined functions append descriptors in code-section order. Each type index
resolves in the existing type section and its declaration flags start clear. -/
def FunctionsAdded (env result : metadata.CodeMetadata) (indices : List U32) : Prop :=
  result = { env with funcs := result.funcs } ∧
    result.funcs.val = env.funcs.val ++ indices.map (fun i => ⟨i, false, false⟩) ∧
    ∀ idx ∈ indices, idx.val < env.types.val.length

end Itasca.Module.Sections

namespace Itasca

open Binary Module.Sections

/-- The function loop adds `count` indices forming a `Rep IndexEncoding` span. -/
@[step]
theorem metadata.decode_function_section_loop.spec (data : Slice U8) (env : metadata.CodeMetadata)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hfuncs : env.funcs.val.length ≤ start.val) :
    metadata.decode_function_section_loop data env count start 0#u32 ⦃ r => match r.1 with
      | .Ok next => ∃ indices, indices.length = count.val ∧
          FunctionsAdded env r.2 indices ∧
          At (Rep IndexEncoding) data start indices next ∧
          r.2.funcs.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  unfold metadata.decode_function_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ ∃ indices,
      indices.length = s.2.2.val ∧ FunctionsAdded env s.1 indices ∧
      At (Rep IndexEncoding) data start indices s.2.1 ∧
      s.1.funcs.val.length ≤ s.2.1.val)
  · rintro ⟨current, pos, i⟩ ⟨hi, indices, hlen, henv, hbytes, hfuncs⟩
    dsimp only at hi hlen henv hbytes hfuncs
    unfold metadata.decode_function_section_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : i.val = count.val := by scalar_tac
      exact ⟨indices, by omega, henv, hbytes, hfuncs⟩
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
        by_cases ht : idx.val < current.types.val.length
        · have cap : current.funcs.val.length < Usize.max := by scalar_tac
          have htypes : current.types = env.types := by rw [henv.1]
          simp [core.result.Result.Insts.CoreOpsTry.branch, lift, Nat.not_le_of_gt ht]
          step as ⟨funcs, hpush⟩
          step as ⟨nextIndex, hinc⟩
          refine ⟨by scalar_tac, ⟨indices ++ [idx], by simp [hlen, hinc], ?_, hbytes.snoc (At.of_u32 hp), ?_⟩, by scalar_tac⟩
          · refine ⟨by rw [henv.1], by simp [hpush, henv.2.1, List.append_assoc], ?_⟩
            intro x hx
            rcases (by simpa using hx : x ∈ indices ∨ x = idx) with hx | rfl
            · exact henv.2.2 x hx
            · simpa [htypes] using ht
          · simp only [hpush, List.length_append, List.length_singleton]; omega
        · simp [core.result.Result.Insts.CoreOpsTry.branch, lift, Nat.le_of_not_gt ht]
  · exact ⟨by simp, [], by simp, ⟨by cases env; rfl, by simp, by simp⟩,
      ⟨[], .nil, Body.Scalar.BytesAt.nil data start hstart⟩, hfuncs⟩

/-- `metadata.decode_function_section` adds the indices of a `VecEncoding IndexEncoding` span with
their resolved signatures. -/
@[step]
theorem metadata.decode_function_section.spec (data : Slice U8) (pos : Usize) (env : metadata.CodeMetadata)
    (hfuncs : env.funcs.val.length ≤ pos.val) :
    metadata.decode_function_section data pos env ⦃ r => match r.1 with
      | .Ok next => ∃ indices, FunctionsAdded env r.2 indices ∧
          At (VecEncoding IndexEncoding) data pos indices next ∧
          r.2.funcs.val.length ≤ next.val
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
      (metadata.decode_function_section_loop.spec data env count start hs.2.2 (by omega))
    simp [metadata.decode_function_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
    rw [hloop]
    cases r with
    | Err e => simp
    | Ok next =>
      obtain ⟨indices, hlen, henv, hb, hf⟩ := hp
      exact ⟨indices, henv, At.vector hc hb hlen, hf⟩

end Itasca

end
