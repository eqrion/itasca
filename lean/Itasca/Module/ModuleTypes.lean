import Itasca.Module.ModuleReaders
import Itasca.Profile.Types

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary

@[step]
theorem module.decode_limits.spec (data : Slice U8) (start : Usize) :
    module.decode_limits data start ⦃ r => ParserPost LimitsEncoding data start r ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data start)
  cases r with
  | Err e =>
      simp [module.decode_limits, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        error.Error.Insts.CoreConvertFromOpError.from, ParserPost]
  | Ok pair =>
      obtain ⟨flag, pos⟩ := pair
      by_cases hzero : flag = 0#u8
      · obtain ⟨r, hu, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
        cases r with
        | Err e =>
            simp [module.decode_limits, hr, hu, hzero, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              error.Error.Insts.CoreConvertFromOpError.from, ParserPost]
        | Ok pair =>
            obtain ⟨min, next⟩ := pair
            simp [module.decode_limits, hr, hu, hzero, core.result.Result.Insts.CoreOpsTry.branch, ParserPost]
            obtain ⟨bytes, hs, hl, hb, he⟩ := hd
            refine ⟨0#u8 :: bytes, .noMax min he, ?_⟩
            simpa [hzero] using (At.byte hp).append ⟨hs, hl, hb⟩
      · by_cases hone : flag = 1#u8
        · obtain ⟨r, hu, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
          cases r with
          | Err e =>
              simp [module.decode_limits, hr, hu, hone, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                error.Error.Insts.CoreConvertFromOpError.from, ParserPost]
          | Ok pair =>
              obtain ⟨min, middle⟩ := pair
              obtain ⟨r, hu', hd'⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data middle)
              cases r with
              | Err e =>
                  simp [module.decode_limits, hr, hu, hu', hone, core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                    error.Error.Insts.CoreConvertFromOpError.from, ParserPost]
              | Ok pair =>
                  obtain ⟨max, next⟩ := pair
                  simp [module.decode_limits, hr, hu, hu', hone,
                    core.result.Result.Insts.CoreOpsTry.branch, ParserPost]
                  obtain ⟨first, hs, hl, hb, he⟩ := hd
                  obtain ⟨rest, hs', hl', hb', he'⟩ := hd'
                  refine ⟨1#u8 :: (first ++ rest), .max min max he he', ?_⟩
                  simpa [hone] using (At.byte hp).append
                    ((show Wasm.BytesAt data pos first middle from ⟨hs, hl, hb⟩).append ⟨hs', hl', hb'⟩)
        · simp [module.decode_limits, hr, core.result.Result.Insts.CoreOpsTry.branch, ParserPost]
          split <;> simp_all [U8.ofNat, UScalar.ofNat, UScalar.ofNatCore]

@[step]
theorem module.decode_global_type.spec (data : Slice U8) (start : Usize)
    (profile : ValidationProfile := .Wasm1) :
    module.decode_global_type data start profile ⦃ r => ParserPost GlobalTypeEncoding data start r ⦄ := by
  obtain ⟨r, ht, hd⟩ := WP.spec_imp_exists (module.decode_value_type.syntax_spec data start profile)
  cases r with
  | Err e =>
      simp [module.decode_global_type, ht, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, ParserPost]
  | Ok pair =>
      obtain ⟨ty, pos⟩ := pair
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data pos)
      cases r with
      | Err e =>
          simp [module.decode_global_type, ht, hr, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            error.Error.Insts.CoreConvertFromOpError.from, ParserPost]
      | Ok pair =>
          obtain ⟨mutability, next⟩ := pair
          obtain ⟨bytes, he, hs⟩ := hd
          have heq : bytes = [valueByte ty] := he
          subst bytes
          by_cases hzero : mutability = 0#u8
          · simp [module.decode_global_type, ht, hr, hzero, core.result.Result.Insts.CoreOpsTry.branch, ParserPost]
            exact ⟨_, rfl, by simpa [hzero, mutByte] using hs.append (At.byte hp)⟩
          · by_cases hone : mutability = 1#u8
            · simp [module.decode_global_type, ht, hr, hone, core.result.Result.Insts.CoreOpsTry.branch, ParserPost]
              exact ⟨_, rfl, by simpa [hone, mutByte] using hs.append (At.byte hp)⟩
            · simp [module.decode_global_type, ht, hr, core.result.Result.Insts.CoreOpsTry.branch, ParserPost]
              split <;> simp_all [U8.ofNat, UScalar.ofNat, UScalar.ofNatCore]

@[step]
theorem module.decode_mem_type.spec (data : Slice U8) (start : Usize) :
    module.decode_mem_type data start ⦃ r => match r with
      | .Ok (ty, next) => At MemTypeEncoding data start ty next ∧
          LimitsValid ty.limits limits.MAX_MEMORY_PAGES
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (module.decode_limits.spec data start)
  cases r with
  | Err e =>
      simp [module.decode_mem_type, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
      obtain ⟨lim, next⟩ := pair
      obtain ⟨r, hv, hp⟩ := WP.spec_imp_exists (limits.validate_limits.spec lim limits.MAX_MEMORY_PAGES)
      cases r with
      | Err e =>
          simp [module.decode_mem_type, hr, hv, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok u =>
          cases u
          simp [module.decode_mem_type, hr, hv, core.result.Result.Insts.CoreOpsTry.branch]
          exact ⟨hd, hp rfl⟩

@[step]
theorem module.decode_table_type.spec (data : Slice U8) (start : Usize)
    (profile : ValidationProfile := .Wasm1) :
    module.decode_table_type data start profile ⦃ r => match r with
      | .Ok (ty, next) => At TableTypeEncoding data start ty next ∧
          LimitsValid ty.limits limits.MAX_TABLE_ELEMS
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (module.decode_elem_type.spec data start profile)
  cases r with
  | Err e =>
      simp [module.decode_table_type, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
      obtain ⟨elem, pos⟩ := pair
      obtain ⟨r, hl, hd⟩ := WP.spec_imp_exists (module.decode_limits.spec data pos)
      cases r with
      | Err e =>
          simp [module.decode_table_type, hr, hl, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
          obtain ⟨lim, next⟩ := pair
          obtain ⟨r, hv, hvalid⟩ := WP.spec_imp_exists (limits.validate_limits.spec lim limits.MAX_TABLE_ELEMS)
          cases r with
          | Err e =>
              simp [module.decode_table_type, hr, hl, hv, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok u =>
              cases u
              simp [module.decode_table_type, hr, hl, hv, core.result.Result.Insts.CoreOpsTry.branch]
              obtain ⟨bytes, hc, hs⟩ := hd
              obtain ⟨eb, ⟨rfl, _⟩, hes⟩ := hp
              refine ⟨⟨elemByte elem :: bytes, ⟨bytes, hc, rfl⟩, ?_⟩, hvalid rfl⟩
              exact hes.append hs

namespace ModuleBinary

theorem At.rep_snoc {α : Type} {R : α → List U8 → Prop} {data start pos next xs x}
    (h : At (Rep R) data start xs pos) (h' : At R data pos x next) :
    At (Rep R) data start (xs ++ [x]) next := by
  obtain ⟨bytes, he, hs⟩ := h
  obtain ⟨last, he', hs'⟩ := h'
  exact ⟨bytes ++ last, he.snoc he', hs.append hs'⟩

end ModuleBinary

theorem module.decode_value_types_loop0.spec (data : Slice U8) (start : Usize)
    (count : U32) (hb : start.val ≤ data.length) (profile : ValidationProfile := .Wasm1) :
    module.decode_value_types_loop0 data profile count (alloc.vec.Vec.new types.ValueType) start 0#u32 ⦃ r =>
      match r with
      | .Ok (out, next) => At (Rep ValueTypeEncoding) data start out.val next ∧
          out.val.length = count.val
      | .Err _ => True ⦄ := by
  unfold module.decode_value_types_loop0
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ s.1.val.length = s.2.2.val ∧
      s.2.1.val = start.val + s.2.2.val ∧
      At (Rep ValueTypeEncoding) data start s.1.val s.2.1)
  · rintro ⟨out, pos, i⟩ ⟨hi, hlen, hpos, hrep⟩
    dsimp only at *
    by_cases hdone : count.val ≤ i.val
    · have he : i ≥ count := by scalar_tac
      simp [module.decode_value_types_loop0.body, he]
      exact ⟨hrep, by omega⟩
    · have he : ¬i ≥ count := by scalar_tac
      obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (module.decode_value_type.syntax_spec data pos profile)
      cases r with
      | Err e =>
          simp [module.decode_value_types_loop0.body, he, hr,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
          obtain ⟨ty, next⟩ := pair
          obtain ⟨bytes, hbytes, hs⟩ := hd
          have hbts : bytes = [valueByte ty] := hbytes
          subst bytes
          have hn : next.val = pos.val + 1 := by simpa using hs.length
          have hb' := hs.bound
          simp [module.decode_value_types_loop0.body, he, hr,
            core.result.Result.Insts.CoreOpsTry.branch]
          step*
          refine ⟨by scalar_tac, ?_, by scalar_tac, ?_, by scalar_tac⟩
          · simp only [out1_post, List.length_append, List.length_singleton]
            scalar_tac
          · rw [out1_post]
            exact hrep.rep_snoc ⟨_, rfl, hs⟩
  · exact ⟨by scalar_tac, rfl, by simp, ⟨[], .nil, Wasm.BytesAt.nil data start hb⟩⟩

@[step]
theorem module.decode_value_types.spec (data : Slice U8) (start : Usize)
    (profile : ValidationProfile := .Wasm1) :
    module.decode_value_types data start none profile ⦃ r => match r with
      | .Ok (out, next) => At (VecEncoding ValueTypeEncoding) data start out.val next
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data start)
  cases r with
  | Err e =>
      simp [module.decode_value_types, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
      obtain ⟨count, pos⟩ := pair
      obtain ⟨r, hv, hp⟩ := WP.spec_imp_exists (module.decode_value_types_loop0.spec data pos count hd.span.2.2 profile)
      cases r with
      | Err e => simp [module.decode_value_types, hr, hv, core.result.Result.Insts.CoreOpsTry.branch]
      | Ok pair =>
          obtain ⟨out, next⟩ := pair
          simp [module.decode_value_types, hr, hv, core.result.Result.Insts.CoreOpsTry.branch]
          obtain ⟨he, hlen⟩ := hp
          obtain ⟨countBytes, hcs, hcl, hcb, hcount⟩ := hd
          obtain ⟨entries, hr, hs⟩ := he
          exact ⟨countBytes ++ entries, ⟨countBytes, entries, by simpa [hlen] using hcount, hr, rfl⟩,
            (show Wasm.BytesAt data start countBytes pos from ⟨hcs, hcl, hcb⟩).append hs⟩

/-- Extraction emits two identical loops for the bounded and unbounded arms. -/
theorem module.decode_value_types_loop1.eq_loop0 (data : Slice U8) (count : U32)
    (out : alloc.vec.Vec types.ValueType) (pos : Usize) (i : U32)
    (profile : ValidationProfile := .Wasm1) :
    module.decode_value_types_loop1 data profile count out pos i =
      module.decode_value_types_loop0 data profile count out pos i := rfl

/-- The same independent vector grammar describes every bound selection. -/
theorem module.decode_value_types.profile_spec (data : Slice U8) (start : Usize)
    (bound : Option (Usize × error.OpError)) (profile : ValidationProfile := .Wasm1) :
    module.decode_value_types data start bound profile ⦃ r => match r with
      | .Ok (out, next) => At (VecEncoding ValueTypeEncoding) data start out.val next ∧
          ∀ limit err, bound = some (limit, err) → out.val.length ≤ limit.val
      | .Err _ => True ⦄ := by
  cases bound with
  | none =>
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (module.decode_value_types.spec data start profile)
      rw [hr]
      cases r <;> simp_all
  | some pair =>
      obtain ⟨limit, err⟩ := pair
      obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data start)
      cases r with
      | Err e =>
          simp [module.decode_value_types, hr, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            error.Error.Insts.CoreConvertFromOpError.from]
      | Ok pair =>
          obtain ⟨count, pos⟩ := pair
          by_cases hbig : count.val > limit.val
          · simp [module.decode_value_types, hr, core.result.Result.Insts.CoreOpsTry.branch, lift, U32.cast_Usize_val_eq, hbig]
          · obtain ⟨r, hv, hp⟩ := WP.spec_imp_exists
              (module.decode_value_types_loop0.spec data pos count hd.span.2.2 profile)
            have hrun : module.decode_value_types data start (some (limit, err)) profile =
                module.decode_value_types_loop0 data profile count (alloc.vec.Vec.new _) pos 0#u32 := by
              simp [module.decode_value_types, hr, core.result.Result.Insts.CoreOpsTry.branch,
                lift, hbig, module.decode_value_types_loop1.eq_loop0]
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
                    (show Wasm.BytesAt data start countBytes pos from ⟨hcs, hcl, hcb⟩).append hs⟩
                · intro limit' err' heq
                  cases heq
                  have hc := U32.cast_Usize_val_eq count
                  scalar_tac

@[step]
theorem module.decode_func_type.spec (data : Slice U8) (start : Usize) :
    module.decode_func_type data start .Wasm1 ⦃ r => match r with
      | .Ok (ty, next) => At FuncTypeEncoding data start ty next ∧ ty.results.val.length ≤ 1
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data start)
  cases r with
  | Err e =>
      simp [module.decode_func_type, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
      obtain ⟨tag, pos⟩ := pair
      by_cases he : tag = 0x60#u8
      · obtain ⟨r, hv, hd⟩ := WP.spec_imp_exists (module.decode_value_types.spec data pos)
        cases r with
        | Err e =>
            simp [module.decode_func_type, hr, he, hv, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok pair =>
            obtain ⟨params, middle⟩ := pair
            obtain ⟨r, hv', hd'⟩ := WP.spec_imp_exists (module.decode_value_types.spec data middle)
            cases r with
            | Err e =>
                simp [module.decode_func_type, hr, he, hv, hv', core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            | Ok pair =>
                obtain ⟨results, next⟩ := pair
                simp [module.decode_func_type, hr, he, hv, hv',
                  core.result.Result.Insts.CoreOpsTry.branch, alloc.vec.Vec.len, limits.MAX_RESULTS]
                split
                · simp
                · rename_i hlen
                  simp only [WP.spec_ok]
                  obtain ⟨paramsBytes, he1, hs1⟩ := hd
                  obtain ⟨resultsBytes, he2, hs2⟩ := hd'
                  refine ⟨⟨0x60#u8 :: (paramsBytes ++ resultsBytes),
                    ⟨paramsBytes, resultsBytes, he1, he2, rfl⟩, ?_⟩, ?_⟩
                  · simpa [he] using (At.byte hp).append (hs1.append hs2)
                  · scalar_tac
      · have hv : tag.val ≠ 96 := by
          intro h
          exact he (UScalar.eq_of_val_eq h)
        simp [module.decode_func_type, hr, hv, core.result.Result.Insts.CoreOpsTry.branch]

/-- Type decoding shares its binary contract across profiles, and records
language restrictions separately from implementation signature bounds. -/
theorem module.decode_func_type.profile_spec (data : Slice U8) (start : Usize)
    (profile : ValidationProfile) :
    module.decode_func_type data start profile ⦃ r => match r with
      | .Ok (ty, next) => At FuncTypeEncoding data start ty next ∧
          Profile.FuncType profile ty ∧ Profile.FuncTypeWithinLimits profile ty
      | .Err _ => True ⦄ := by
  cases profile with
  | Wasm1 =>
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (module.decode_func_type.spec data start)
      rw [hr]
      cases r <;> simpa [Profile.FuncType, Profile.FuncTypeWithinLimits] using hp
  | Wasm2 =>
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data start)
      cases r with
      | Err e =>
          simp [module.decode_func_type, hr, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            error.Error.Insts.CoreConvertFromOpError.from]
      | Ok pair =>
          obtain ⟨tag, pos⟩ := pair
          by_cases he : tag = 0x60#u8
          · obtain ⟨r, hv, hd⟩ := WP.spec_imp_exists (module.decode_value_types.profile_spec
              data pos (some (limits.MAX_MULTI_VALUE_PARAMS, error.OpError.TooManyParams)) .Wasm2)
            cases r with
            | Err e =>
                simp [module.decode_func_type, hr, he, hv, core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            | Ok pair =>
                obtain ⟨params, middle⟩ := pair
                obtain ⟨r, hv', hd'⟩ := WP.spec_imp_exists (module.decode_value_types.profile_spec
                  data middle (some (limits.MAX_MULTI_VALUE_RESULTS, error.OpError.TooManyResults)) .Wasm2)
                cases r with
                | Err e =>
                    simp [module.decode_func_type, hr, he, hv, hv', core.result.Result.Insts.CoreOpsTry.branch,
                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                | Ok pair =>
                    obtain ⟨results, next⟩ := pair
                    have hrun : module.decode_func_type data start .Wasm2 =
                        .ok (.Ok ({ params, results }, next)) := by
                      simp [module.decode_func_type, hr, he, hv, hv',
                        core.result.Result.Insts.CoreOpsTry.branch]
                    rw [hrun]
                    simp only [WP.spec_ok]
                    obtain ⟨paramsBytes, he1, hs1⟩ := hd.1
                    obtain ⟨resultsBytes, he2, hs2⟩ := hd'.1
                    refine ⟨⟨0x60#u8 :: (paramsBytes ++ resultsBytes),
                      ⟨paramsBytes, resultsBytes, he1, he2, rfl⟩, ?_⟩,
                      trivial, hd.2 _ _ rfl, hd'.2 _ _ rfl⟩
                    simpa [he] using (At.byte hp).append (hs1.append hs2)
          · have hv : tag.val ≠ 96 := by
              intro h
              exact he (UScalar.eq_of_val_eq h)
            simp [module.decode_func_type, hr, hv, core.result.Result.Insts.CoreOpsTry.branch]

theorem module.decode_global_type.allowed_spec (data : Slice U8) (start : Usize)
    (profile : ValidationProfile := .Wasm1) :
    module.decode_global_type data start profile ⦃ r => match r with
      | .Ok (ty, next) => At GlobalTypeEncoding data start ty next ∧ ValueTypeAllowed profile ty.valtype
      | .Err _ => True ⦄ := by
  obtain ⟨r, ht, hd⟩ := WP.spec_imp_exists (module.decode_value_type.spec data start profile)
  cases r with
  | Err e =>
      simp [module.decode_global_type, ht, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, ParserPost]
  | Ok pair =>
      obtain ⟨ty, pos⟩ := pair
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data pos)
      cases r with
      | Err e =>
          simp [module.decode_global_type, ht, hr, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            error.Error.Insts.CoreConvertFromOpError.from, ParserPost]
      | Ok pair =>
          obtain ⟨mutability, next⟩ := pair
          obtain ⟨bytes, ⟨he, ha⟩, hs⟩ := hd
          have heq : bytes = [valueByte ty] := he
          subst bytes
          by_cases hzero : mutability = 0#u8
          · simp [module.decode_global_type, ht, hr, hzero, core.result.Result.Insts.CoreOpsTry.branch, ParserPost]
            exact ⟨⟨_, rfl, by simpa [hzero, mutByte] using hs.append (At.byte hp)⟩, ha⟩
          · by_cases hone : mutability = 1#u8
            · simp [module.decode_global_type, ht, hr, hone, core.result.Result.Insts.CoreOpsTry.branch, ParserPost]
              exact ⟨⟨_, rfl, by simpa [hone, mutByte] using hs.append (At.byte hp)⟩, ha⟩
            · simp [module.decode_global_type, ht, hr, core.result.Result.Insts.CoreOpsTry.branch, ParserPost]
              split <;> simp_all [U8.ofNat, UScalar.ofNat, UScalar.ofNatCore]


theorem module.decode_table_type.allowed_spec (data : Slice U8) (start : Usize)
    (profile : ValidationProfile := .Wasm1) :
    module.decode_table_type data start profile ⦃ r => match r with
      | .Ok (ty, next) => (At TableTypeEncoding data start ty next ∧
          LimitsValid ty.limits limits.MAX_TABLE_ELEMS) ∧ ElemTypeAllowed profile ty.elem
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (module.decode_elem_type.spec data start profile)
  cases r with
  | Err e =>
      simp [module.decode_table_type, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
      obtain ⟨elem, pos⟩ := pair
      obtain ⟨r, hl, hd⟩ := WP.spec_imp_exists (module.decode_limits.spec data pos)
      cases r with
      | Err e =>
          simp [module.decode_table_type, hr, hl, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
          obtain ⟨lim, next⟩ := pair
          obtain ⟨r, hv, hvalid⟩ := WP.spec_imp_exists (limits.validate_limits.spec lim limits.MAX_TABLE_ELEMS)
          cases r with
          | Err e =>
              simp [module.decode_table_type, hr, hl, hv, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok u =>
              cases u
              have hrun : module.decode_table_type data start profile =
                  .ok (.Ok ({ limits := lim, elem }, next)) := by
                simp [module.decode_table_type, hr, hl, hv, core.result.Result.Insts.CoreOpsTry.branch]
              rw [hrun]
              simp only [WP.spec_ok]
              obtain ⟨bytes, hc, hs⟩ := hd
              obtain ⟨eb, ⟨rfl, ha⟩, hes⟩ := hp
              refine ⟨⟨⟨elemByte elem :: bytes, ⟨bytes, hc, rfl⟩, ?_⟩, hvalid rfl⟩, ha⟩
              exact hes.append hs

private theorem module.decode_value_types_loop0.allowed_only_spec (data : Slice U8)
    (profile : ValidationProfile) (count : U32) (start : Usize) :
    module.decode_value_types_loop0 data profile count (alloc.vec.Vec.new _) start 0#u32 ⦃ r =>
      match r with
      | .Ok (out, _) => ∀ ty ∈ out.val, ValueTypeAllowed profile ty
      | .Err _ => True ⦄ := by
  unfold module.decode_value_types_loop0
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ s.1.val.length = s.2.2.val ∧
      ∀ ty ∈ s.1.val, ValueTypeAllowed profile ty)
  · rintro ⟨out, pos, i⟩ ⟨hi, hlen, hallowed⟩
    dsimp only at *
    unfold module.decode_value_types_loop0.body
    split
    · simpa only [WP.spec_ok] using hallowed
    · have hcapacity : out.val.length < Usize.max := by scalar_tac
      obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (module.decode_value_type.spec data pos profile)
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
            (ControlFlow (alloc.vec.Vec types.ValueType × Usize × U32)
              (core.result.Result (alloc.vec.Vec types.ValueType × Usize) error.Error)))) ⦃ _ ⦄
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

private theorem module.decode_value_types.allowed_only_spec (data : Slice U8) (start : Usize)
    (bound : Option (Usize × error.OpError)) (profile : ValidationProfile) :
    module.decode_value_types data start bound profile ⦃ r => match r with
      | .Ok (out, _) => ∀ ty ∈ out.val, ValueTypeAllowed profile ty
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data start)
  cases r with
  | Err e => simp [module.decode_value_types, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    obtain ⟨count, pos⟩ := pair
    obtain ⟨r, hloop, ha⟩ := WP.spec_imp_exists
      (module.decode_value_types_loop0.allowed_only_spec data profile count pos)
    cases bound with
    | none => simpa [module.decode_value_types, hr, core.result.Result.Insts.CoreOpsTry.branch,
        hloop] using ha
    | some pair =>
      obtain ⟨limit, err⟩ := pair
      by_cases hbig : count.val > limit.val
      · simp [module.decode_value_types, hr, core.result.Result.Insts.CoreOpsTry.branch, lift, hbig]
      · simpa [module.decode_value_types, hr, core.result.Result.Insts.CoreOpsTry.branch,
          lift, hbig, module.decode_value_types_loop1.eq_loop0, hloop] using ha

/-- A vector retains both its exact byte grammar and all selected-profile types. -/
theorem module.decode_value_types.allowed_spec (data : Slice U8) (start : Usize)
    (bound : Option (Usize × error.OpError)) (profile : ValidationProfile) :
    module.decode_value_types data start bound profile ⦃ r => match r with
      | .Ok (out, next) =>
          (At (VecEncoding ValueTypeEncoding) data start out.val next ∧
            ∀ limit err, bound = some (limit, err) → out.val.length ≤ limit.val) ∧
          ∀ ty ∈ out.val, ValueTypeAllowed profile ty
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists
    (module.decode_value_types.profile_spec data start bound profile)
  obtain ⟨r', hr', ha⟩ := WP.spec_imp_exists
    (module.decode_value_types.allowed_only_spec data start bound profile)
  have he : r' = r := by simpa only [Result.ok.injEq] using hr'.symm.trans hr
  subst r'
  rw [hr]
  simp only [WP.spec_ok]
  cases r with
  | Err _ => trivial
  | Ok pair => exact ⟨hp, ha⟩

private theorem module.decode_func_type.allowed_only_spec (data : Slice U8) (start : Usize)
    (profile : ValidationProfile) :
    module.decode_func_type data start profile ⦃ r => match r with
      | .Ok (ft, _) => ∀ ty ∈ ft.params.val ++ ft.results.val, ValueTypeAllowed profile ty
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data start)
  cases r with
  | Err e => simp [module.decode_func_type, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    obtain ⟨tag, pos⟩ := pair
    by_cases he : tag = 0x60#u8
    · let pbound : Option (Usize × error.OpError) := match profile with
        | .Wasm1 => none
        | .Wasm2 => some (limits.MAX_MULTI_VALUE_PARAMS, error.OpError.TooManyParams)
      let rbound : Option (Usize × error.OpError) := match profile with
        | .Wasm1 => none
        | .Wasm2 => some (limits.MAX_MULTI_VALUE_RESULTS, error.OpError.TooManyResults)
      obtain ⟨r, hp, hap⟩ := WP.spec_imp_exists
        (module.decode_value_types.allowed_only_spec data pos pbound profile)
      cases r with
      | Err e =>
        cases profile <;> simp_all [module.decode_func_type, pbound,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
        obtain ⟨params, middle⟩ := pair
        obtain ⟨r, hres, har⟩ := WP.spec_imp_exists
          (module.decode_value_types.allowed_only_spec data middle rbound profile)
        cases r with
        | Err e =>
          cases profile <;> simp_all [module.decode_func_type, pbound, rbound,
            core.result.Result.Insts.CoreOpsTry.branch,
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
            simp only [pbound, rbound] at hp hres
            simp [module.decode_func_type, hr, he, hp, hres,
              core.result.Result.Insts.CoreOpsTry.branch]
            split
            · simp
            · simpa [List.mem_append] using hall
          | Wasm2 =>
            simp only [pbound, rbound] at hp hres
            simpa [module.decode_func_type, hr, he, hp, hres,
              core.result.Result.Insts.CoreOpsTry.branch] using hall
    · have htag : tag.val ≠ 96 := fun h => he (UScalar.eq_of_val_eq h)
      simp [module.decode_func_type, hr, htag, core.result.Result.Insts.CoreOpsTry.branch]

/-- The type-section parser additionally retains profile restrictions on every
parameter and result type. -/
theorem module.decode_func_type.allowed_spec (data : Slice U8) (start : Usize)
    (profile : ValidationProfile) :
    module.decode_func_type data start profile ⦃ r => match r with
      | .Ok (ft, next) =>
          (At FuncTypeEncoding data start ft next ∧ Profile.FuncType profile ft ∧
            Profile.FuncTypeWithinLimits profile ft) ∧
          ∀ ty ∈ ft.params.val ++ ft.results.val, ValueTypeAllowed profile ty
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (module.decode_func_type.profile_spec data start profile)
  obtain ⟨r', hr', ha⟩ := WP.spec_imp_exists (module.decode_func_type.allowed_only_spec data start profile)
  have he : r' = r := by simpa only [Result.ok.injEq] using hr'.symm.trans hr
  subst r'
  rw [hr]
  simp only [WP.spec_ok]
  cases r with
  | Err _ => trivial
  | Ok pair => exact ⟨hp, ha⟩

end Itasca
