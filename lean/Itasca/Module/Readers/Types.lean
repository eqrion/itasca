import Itasca.Module.Readers.Basic
import Itasca.Profile.Types

/-!
# Limit, memory, table, global and function type readers

Soundness specs for `metadata.decode_limits`, `metadata.decode_mem_type`, `metadata.decode_table_type`,
`metadata.decode_global_type`, `metadata.decode_value_types` and `metadata.decode_func_type`. Results
are `At` spans of the independent grammar, together with the limit bounds. The `allowed_spec` and
`profile_spec` forms add the profile's value-type, reference-type and signature restrictions for
both profiles. Completeness is in `Module/Readers/TypesComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary

/-- `metadata.decode_limits` returns a `LimitsEncoding` span. -/
@[step]
theorem metadata.decode_limits.spec (data : Slice U8) (start : Usize) :
    metadata.decode_limits data start ⦃ r => ParserPost LimitsEncoding data start r ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data start)
  cases r with
  | Err e =>
      simp [metadata.decode_limits, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        error.Error.Insts.CoreConvertFromOpError.from, ParserPost]
  | Ok pair =>
      obtain ⟨flag, pos⟩ := pair
      by_cases hzero : flag = 0#u8
      · obtain ⟨r, hu, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
        cases r with
        | Err e =>
            simp [metadata.decode_limits, hr, hu, hzero, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              error.Error.Insts.CoreConvertFromOpError.from, ParserPost]
        | Ok pair =>
            obtain ⟨min, next⟩ := pair
            simp [metadata.decode_limits, hr, hu, hzero, core.result.Result.Insts.CoreOpsTry.branch, ParserPost]
            obtain ⟨bytes, hs, hl, hb, he⟩ := hd
            refine ⟨0#u8 :: bytes, .noMax min he, ?_⟩
            simpa [hzero] using (At.byte hp).append ⟨hs, hl, hb⟩
      · by_cases hone : flag = 1#u8
        · obtain ⟨r, hu, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
          cases r with
          | Err e =>
              simp [metadata.decode_limits, hr, hu, hone, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                error.Error.Insts.CoreConvertFromOpError.from, ParserPost]
          | Ok pair =>
              obtain ⟨min, middle⟩ := pair
              obtain ⟨r, hu', hd'⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data middle)
              cases r with
              | Err e =>
                  simp [metadata.decode_limits, hr, hu, hu', hone, core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                    error.Error.Insts.CoreConvertFromOpError.from, ParserPost]
              | Ok pair =>
                  obtain ⟨max, next⟩ := pair
                  simp [metadata.decode_limits, hr, hu, hu', hone,
                    core.result.Result.Insts.CoreOpsTry.branch, ParserPost]
                  obtain ⟨first, hs, hl, hb, he⟩ := hd
                  obtain ⟨rest, hs', hl', hb', he'⟩ := hd'
                  refine ⟨1#u8 :: (first ++ rest), .max min max he he', ?_⟩
                  simpa [hone] using (At.byte hp).append
                    ((show Wasm1.BytesAt data pos first middle from ⟨hs, hl, hb⟩).append ⟨hs', hl', hb'⟩)
        · simp [metadata.decode_limits, hr, core.result.Result.Insts.CoreOpsTry.branch, ParserPost]
          split <;> simp_all [U8.ofNat, UScalar.ofNat, UScalar.ofNatCore]

/-- `metadata.decode_mem_type` returns a `MemTypeEncoding` span whose limits are within
`limits.MAX_MEMORY_PAGES`. -/
@[step]
theorem metadata.decode_mem_type.spec (data : Slice U8) (start : Usize) :
    metadata.decode_mem_type data start ⦃ r => match r with
      | .Ok (ty, next) => At MemTypeEncoding data start ty next ∧
          LimitsValid ty.limits limits.MAX_MEMORY_PAGES
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (metadata.decode_limits.spec data start)
  cases r with
  | Err e =>
      simp [metadata.decode_mem_type, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
      obtain ⟨lim, next⟩ := pair
      obtain ⟨r, hv, hp⟩ := WP.spec_imp_exists (limits.validate_limits.spec lim limits.MAX_MEMORY_PAGES)
      cases r with
      | Err e =>
          simp [metadata.decode_mem_type, hr, hv, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok u =>
          cases u
          simp [metadata.decode_mem_type, hr, hv, core.result.Result.Insts.CoreOpsTry.branch]
          exact ⟨hd, hp rfl⟩

namespace ModuleBinary

/-- A repetition span extends by one element at its end. -/
theorem At.rep_snoc {α : Type} {R : α → List U8 → Prop} {data start pos next xs x}
    (h : At (Rep R) data start xs pos) (h' : At R data pos x next) :
    At (Rep R) data start (xs ++ [x]) next := by
  obtain ⟨bytes, he, hs⟩ := h
  obtain ⟨last, he', hs'⟩ := h'
  exact ⟨bytes ++ last, he.snoc he', hs.append hs'⟩

end ModuleBinary

/-- The counted loop returns `count` value types forming a `Rep ValueTypeEncoding` span. -/
theorem metadata.decode_value_types_loop.spec (data : Slice U8) (start : Usize)
    (count : U32) (hb : start.val ≤ data.length) (profile : ValidationProfile := .Wasm1) :
    metadata.decode_value_types_loop data profile count (alloc.vec.Vec.new wasm_types.ValueType) start 0#u32 ⦃ r =>
      match r with
      | .Ok (out, next) => At (Rep ValueTypeEncoding) data start out.val next ∧
          out.val.length = count.val
      | .Err _ => True ⦄ := by
  unfold metadata.decode_value_types_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ s.1.val.length = s.2.2.val ∧
      s.2.1.val = start.val + s.2.2.val ∧
      At (Rep ValueTypeEncoding) data start s.1.val s.2.1)
  · rintro ⟨out, pos, i⟩ ⟨hi, hlen, hpos, hrep⟩
    dsimp only at *
    by_cases hdone : count.val ≤ i.val
    · have he : i ≥ count := by scalar_tac
      simp [metadata.decode_value_types_loop.body, he]
      exact ⟨hrep, by omega⟩
    · have he : ¬i ≥ count := by scalar_tac
      obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (metadata.decode_value_type.syntax_spec data pos profile)
      cases r with
      | Err e =>
          simp [metadata.decode_value_types_loop.body, he, hr,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
          obtain ⟨ty, next⟩ := pair
          obtain ⟨bytes, hbytes, hs⟩ := hd
          have hbts : bytes = [valueByte ty] := hbytes
          subst bytes
          have hn : next.val = pos.val + 1 := by simpa using hs.length
          have hb' := hs.bound
          simp [metadata.decode_value_types_loop.body, he, hr,
            core.result.Result.Insts.CoreOpsTry.branch]
          step*
          refine ⟨by scalar_tac, ?_, by scalar_tac, ?_, by scalar_tac⟩
          · simp only [out1_post, List.length_append, List.length_singleton]
            scalar_tac
          · rw [out1_post]
            exact hrep.rep_snoc ⟨_, rfl, hs⟩
  · exact ⟨by scalar_tac, rfl, by simp, ⟨[], .nil, Wasm1.BytesAt.nil data start hb⟩⟩

/-- `metadata.decode_value_types` returns a `VecEncoding ValueTypeEncoding` span within the length
bound. -/
theorem metadata.decode_value_types.spec (data : Slice U8) (start : Usize) (limit : Usize)
    (err : error.OpError) (profile : ValidationProfile) :
    metadata.decode_value_types data start limit err profile ⦃ r => match r with
      | .Ok (out, next) => At (VecEncoding ValueTypeEncoding) data start out.val next ∧
          out.val.length ≤ limit.val
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data start)
  cases r with
  | Err e =>
      simp [metadata.decode_value_types, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
      obtain ⟨count, pos⟩ := pair
      by_cases hbig : count.val > limit.val
      · simp [metadata.decode_value_types, hr, core.result.Result.Insts.CoreOpsTry.branch, lift, hbig]
      · obtain ⟨r, hv, hp⟩ := WP.spec_imp_exists
          (metadata.decode_value_types_loop.spec data pos count hd.span.2.2 profile)
        have hrun : metadata.decode_value_types data start limit err profile =
            metadata.decode_value_types_loop data profile count (alloc.vec.Vec.new _) pos 0#u32 := by
          simp [metadata.decode_value_types, hr, core.result.Result.Insts.CoreOpsTry.branch, lift, hbig]
        rw [hrun, hv]
        cases r with
        | Err e => simp
        | Ok pair =>
            obtain ⟨out, next⟩ := pair
            obtain ⟨he, hlen⟩ := hp
            simp only [WP.spec_ok]
            constructor
            · obtain ⟨countBytes, hcs, hcl, hcb, hcount⟩ := hd
              obtain ⟨entries, hr, hs⟩ := he
              exact ⟨countBytes ++ entries,
                ⟨countBytes, entries, by simpa [hlen] using hcount, hr, rfl⟩,
                (show Wasm1.BytesAt data start countBytes pos from ⟨hcs, hcl, hcb⟩).append hs⟩
            · have hc := U32.cast_Usize_val_eq count
              scalar_tac

/-- `metadata.decode_func_type` returns a `FuncTypeEncoding` span in either profile. The result
satisfies the profile's language restriction (`Profile.FuncType`) and the implementation
signature cap (`Profile.FuncTypeWithinLimits`) as separate facts. -/
@[step]
theorem metadata.decode_func_type.profile_spec (data : Slice U8) (start : Usize)
    (profile : ValidationProfile) :
    metadata.decode_func_type data start profile ⦃ r => match r with
      | .Ok (ty, next) => At FuncTypeEncoding data start ty next ∧
          Profile.FuncType profile ty ∧ Profile.FuncTypeWithinLimits ty
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data start)
  cases r with
  | Err e =>
      simp [metadata.decode_func_type, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
      obtain ⟨tag, pos⟩ := pair
      by_cases he : tag = 0x60#u8
      · obtain ⟨r, hv, hd⟩ := WP.spec_imp_exists (metadata.decode_value_types.spec
          data pos limits.MAX_MULTI_VALUE_PARAMS error.OpError.TooManyParams profile)
        cases r with
        | Err e =>
            simp [metadata.decode_func_type, hr, he, hv, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok pair =>
            obtain ⟨params, middle⟩ := pair
            obtain ⟨r, hv', hd'⟩ := WP.spec_imp_exists (metadata.decode_value_types.spec
              data middle limits.MAX_MULTI_VALUE_RESULTS error.OpError.TooManyResults profile)
            cases r with
            | Err e =>
                simp [metadata.decode_func_type, hr, he, hv, hv', core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            | Ok pair =>
                obtain ⟨results, next⟩ := pair
                obtain ⟨paramsBytes, he1, hs1⟩ := hd.1
                obtain ⟨resultsBytes, he2, hs2⟩ := hd'.1
                have hat : At FuncTypeEncoding data start { params, results } next :=
                  ⟨0x60#u8 :: (paramsBytes ++ resultsBytes),
                    ⟨paramsBytes, resultsBytes, he1, he2, rfl⟩,
                    by simpa [he] using (At.byte hp).append (hs1.append hs2)⟩
                have hlimits : Profile.FuncTypeWithinLimits { params, results } :=
                  ⟨hd.2, hd'.2⟩
                cases profile with
                | Wasm1 =>
                    simp [metadata.decode_func_type, hr, he, hv, hv',
                      core.result.Result.Insts.CoreOpsTry.branch, alloc.vec.Vec.len, limits.MAX_RESULTS]
                    split
                    · simp
                    · simp only [WP.spec_ok]
                      exact ⟨hat, by simp [Profile.FuncType]; scalar_tac, hlimits⟩
                | Wasm2 =>
                    simp [metadata.decode_func_type, hr, he, hv, hv',
                      core.result.Result.Insts.CoreOpsTry.branch]
                    exact ⟨hat, trivial, hlimits⟩
      · have hv : tag.val ≠ 96 := by
          intro h
          exact he (UScalar.eq_of_val_eq h)
        simp [metadata.decode_func_type, hr, hv, core.result.Result.Insts.CoreOpsTry.branch]

/-- `metadata.decode_global_type` returns a `GlobalTypeEncoding` span whose value type the profile
allows. -/
theorem metadata.decode_global_type.allowed_spec (data : Slice U8) (start : Usize)
    (profile : ValidationProfile := .Wasm1) :
    metadata.decode_global_type data start profile ⦃ r => match r with
      | .Ok (ty, next) => At GlobalTypeEncoding data start ty next ∧ ValueTypeAllowed profile ty.valtype
      | .Err _ => True ⦄ := by
  obtain ⟨r, ht, hd⟩ := WP.spec_imp_exists (metadata.decode_value_type.spec data start profile)
  cases r with
  | Err e =>
      simp [metadata.decode_global_type, ht, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
      obtain ⟨ty, pos⟩ := pair
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data pos)
      cases r with
      | Err e =>
          simp [metadata.decode_global_type, ht, hr, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            error.Error.Insts.CoreConvertFromOpError.from]
      | Ok pair =>
          obtain ⟨mutability, next⟩ := pair
          obtain ⟨bytes, ⟨he, ha⟩, hs⟩ := hd
          have heq : bytes = [valueByte ty] := he
          subst bytes
          by_cases hzero : mutability = 0#u8
          · simp [metadata.decode_global_type, ht, hr, hzero, core.result.Result.Insts.CoreOpsTry.branch]
            exact ⟨⟨_, rfl, by simpa [hzero, mutByte] using hs.append (At.byte hp)⟩, ha⟩
          · by_cases hone : mutability = 1#u8
            · simp [metadata.decode_global_type, ht, hr, hone, core.result.Result.Insts.CoreOpsTry.branch]
              exact ⟨⟨_, rfl, by simpa [hone, mutByte] using hs.append (At.byte hp)⟩, ha⟩
            · simp [metadata.decode_global_type, ht, hr, core.result.Result.Insts.CoreOpsTry.branch]
              split <;> simp_all [U8.ofNat, UScalar.ofNat, UScalar.ofNatCore]

/-- `metadata.decode_table_type.spec` plus the profile allowing the element type. -/
theorem metadata.decode_table_type.allowed_spec (data : Slice U8) (start : Usize)
    (profile : ValidationProfile := .Wasm1) :
    metadata.decode_table_type data start profile ⦃ r => match r with
      | .Ok (ty, next) => (At TableTypeEncoding data start ty next ∧
          LimitsValid ty.limits limits.MAX_TABLE_ELEMS) ∧ ElemTypeAllowed profile ty.elem
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (metadata.decode_elem_type.spec data start profile)
  cases r with
  | Err e =>
      simp [metadata.decode_table_type, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
      obtain ⟨elem, pos⟩ := pair
      obtain ⟨r, hl, hd⟩ := WP.spec_imp_exists (metadata.decode_limits.spec data pos)
      cases r with
      | Err e =>
          simp [metadata.decode_table_type, hr, hl, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
          obtain ⟨lim, next⟩ := pair
          obtain ⟨r, hv, hvalid⟩ := WP.spec_imp_exists (limits.validate_limits.spec lim limits.MAX_TABLE_ELEMS)
          cases r with
          | Err e =>
              simp [metadata.decode_table_type, hr, hl, hv, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok u =>
              cases u
              have hrun : metadata.decode_table_type data start profile =
                  .ok (.Ok ({ limits := lim, elem }, next)) := by
                simp [metadata.decode_table_type, hr, hl, hv, core.result.Result.Insts.CoreOpsTry.branch]
              rw [hrun]
              simp only [WP.spec_ok]
              obtain ⟨bytes, hc, hs⟩ := hd
              obtain ⟨eb, ⟨rfl, ha⟩, hes⟩ := hp
              refine ⟨⟨⟨elemByte elem :: bytes, ⟨bytes, hc, rfl⟩, ?_⟩, hvalid rfl⟩, ha⟩
              exact hes.append hs

private theorem metadata.decode_value_types_loop.allowed_only_spec (data : Slice U8)
    (profile : ValidationProfile) (count : U32) (start : Usize) :
    metadata.decode_value_types_loop data profile count (alloc.vec.Vec.new _) start 0#u32 ⦃ r =>
      match r with
      | .Ok (out, _) => ∀ ty ∈ out.val, ValueTypeAllowed profile ty
      | .Err _ => True ⦄ := by
  unfold metadata.decode_value_types_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ s.1.val.length = s.2.2.val ∧
      ∀ ty ∈ s.1.val, ValueTypeAllowed profile ty)
  · rintro ⟨out, pos, i⟩ ⟨hi, hlen, hallowed⟩
    dsimp only at *
    unfold metadata.decode_value_types_loop.body
    split
    · simpa only [WP.spec_ok] using hallowed
    · have hcapacity : out.val.length < Usize.max := by scalar_tac
      obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (metadata.decode_value_type.spec data pos profile)
      rw [hr]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
        obtain ⟨ty, next⟩ := pair
        obtain ⟨_, ⟨_, ha⟩, _⟩ := hd
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        change (do
          let out1 ← alloc.vec.Vec.push out ty
          let i1 ← i + 1#u32
          (.ok (.cont (out1, next, i1)) : Result
            (ControlFlow (alloc.vec.Vec wasm_types.ValueType × Usize × U32)
              (core.result.Result (alloc.vec.Vec wasm_types.ValueType × Usize) error.Error)))) ⦃ _ ⦄
        step
        step
        refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
        · simp only [out1_post, List.length_append, List.length_singleton]
          scalar_tac
        · intro value hm
          rw [out1_post] at hm
          rcases List.mem_append.mp hm with hm | hm
          · exact hallowed value hm
          · simpa [List.mem_singleton.mp hm] using ha
  · exact ⟨by simp, by simp, by simp⟩

private theorem metadata.decode_value_types.allowed_only_spec (data : Slice U8) (start : Usize)
    (limit : Usize) (err : error.OpError) (profile : ValidationProfile) :
    metadata.decode_value_types data start limit err profile ⦃ r => match r with
      | .Ok (out, _) => ∀ ty ∈ out.val, ValueTypeAllowed profile ty
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data start)
  cases r with
  | Err e => simp [metadata.decode_value_types, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    obtain ⟨count, pos⟩ := pair
    obtain ⟨r, hloop, ha⟩ := WP.spec_imp_exists
      (metadata.decode_value_types_loop.allowed_only_spec data profile count pos)
    by_cases hbig : count.val > limit.val
    · simp [metadata.decode_value_types, hr, core.result.Result.Insts.CoreOpsTry.branch, lift, hbig]
    · simpa [metadata.decode_value_types, hr, core.result.Result.Insts.CoreOpsTry.branch,
        lift, hbig, hloop] using ha

private theorem metadata.decode_func_type.allowed_only_spec (data : Slice U8) (start : Usize)
    (profile : ValidationProfile) :
    metadata.decode_func_type data start profile ⦃ r => match r with
      | .Ok (ft, _) => ∀ ty ∈ ft.params.val ++ ft.results.val, ValueTypeAllowed profile ty
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data start)
  cases r with
  | Err e => simp [metadata.decode_func_type, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    obtain ⟨tag, pos⟩ := pair
    by_cases he : tag = 0x60#u8
    · obtain ⟨r, hp, hap⟩ := WP.spec_imp_exists (metadata.decode_value_types.allowed_only_spec
        data pos limits.MAX_MULTI_VALUE_PARAMS error.OpError.TooManyParams profile)
      cases r with
      | Err e =>
        simp_all [metadata.decode_func_type, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
        obtain ⟨params, middle⟩ := pair
        obtain ⟨r, hres, har⟩ := WP.spec_imp_exists (metadata.decode_value_types.allowed_only_spec
          data middle limits.MAX_MULTI_VALUE_RESULTS error.OpError.TooManyResults profile)
        cases r with
        | Err e =>
          simp_all [metadata.decode_func_type, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok pair =>
          obtain ⟨results, next⟩ := pair
          have hall : ∀ ty ∈ params.val ++ results.val, ValueTypeAllowed profile ty := by
            intro ty hm
            rcases List.mem_append.mp hm with hm | hm
            · exact hap ty hm
            · exact har ty hm
          cases profile with
          | Wasm1 =>
            simp [metadata.decode_func_type, hr, he, hp, hres,
              core.result.Result.Insts.CoreOpsTry.branch]
            split
            · simp
            · simpa [List.mem_append] using hall
          | Wasm2 =>
            simpa [metadata.decode_func_type, hr, he, hp, hres,
              core.result.Result.Insts.CoreOpsTry.branch] using hall
    · have htag : tag.val ≠ 96 := fun h => he (UScalar.eq_of_val_eq h)
      simp [metadata.decode_func_type, hr, htag, core.result.Result.Insts.CoreOpsTry.branch]

/-- `metadata.decode_func_type.profile_spec` plus the profile allowing every parameter and result
type. -/
theorem metadata.decode_func_type.allowed_spec (data : Slice U8) (start : Usize)
    (profile : ValidationProfile) :
    metadata.decode_func_type data start profile ⦃ r => match r with
      | .Ok (ft, next) =>
          (At FuncTypeEncoding data start ft next ∧ Profile.FuncType profile ft ∧
            Profile.FuncTypeWithinLimits ft) ∧
          ∀ ty ∈ ft.params.val ++ ft.results.val, ValueTypeAllowed profile ty
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (metadata.decode_func_type.profile_spec data start profile)
  obtain ⟨r', hr', ha⟩ := WP.spec_imp_exists (metadata.decode_func_type.allowed_only_spec data start profile)
  have he : r' = r := by simpa only [Result.ok.injEq] using hr'.symm.trans hr
  subst r'
  rw [hr]
  simp only [WP.spec_ok]
  cases r with
  | Err _ => trivial
  | Ok pair => exact ⟨hp, ha⟩

end Itasca
