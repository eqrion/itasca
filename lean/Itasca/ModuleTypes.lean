import Itasca.ModuleReaders

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
        · simp [module.decode_limits, hr, hzero, hone, core.result.Result.Insts.CoreOpsTry.branch, ParserPost]

@[step]
theorem module.decode_global_type.spec (data : Slice U8) (start : Usize) :
    module.decode_global_type data start ⦃ r => ParserPost GlobalTypeEncoding data start r ⦄ := by
  obtain ⟨r, ht, hd⟩ := WP.spec_imp_exists (module.decode_value_type.spec data start)
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
            · simp [module.decode_global_type, ht, hr, hzero, hone, core.result.Result.Insts.CoreOpsTry.branch, ParserPost]
              exact ⟨_, rfl, by simpa [hone, mutByte] using hs.append (At.byte hp)⟩
            · simp [module.decode_global_type, ht, hr, hzero, hone, core.result.Result.Insts.CoreOpsTry.branch, ParserPost]

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
theorem module.decode_table_type.spec (data : Slice U8) (start : Usize) :
    module.decode_table_type data start ⦃ r => match r with
      | .Ok (ty, next) => At TableTypeEncoding data start ty next ∧
          LimitsValid ty.limits limits.MAX_TABLE_ELEMS
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data start)
  cases r with
  | Err e =>
      simp [module.decode_table_type, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
      obtain ⟨tag, pos⟩ := pair
      by_cases he : tag = 0x70#u8
      · obtain ⟨r, hl, hd⟩ := WP.spec_imp_exists (module.decode_limits.spec data pos)
        cases r with
        | Err e =>
            simp [module.decode_table_type, hr, he, hl, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok pair =>
            obtain ⟨lim, next⟩ := pair
            obtain ⟨r, hv, hvalid⟩ := WP.spec_imp_exists (limits.validate_limits.spec lim limits.MAX_TABLE_ELEMS)
            cases r with
            | Err e =>
                simp [module.decode_table_type, hr, he, hl, hv, core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            | Ok u =>
                cases u
                simp [module.decode_table_type, hr, he, hl, hv, core.result.Result.Insts.CoreOpsTry.branch]
                obtain ⟨bytes, hc, hs⟩ := hd
                refine ⟨⟨0x70#u8 :: bytes, ⟨bytes, hc, rfl⟩, ?_⟩, hvalid rfl⟩
                simpa [he] using (At.byte hp).append hs
      · have hv : tag.val ≠ 112 := by
          intro h
          exact he (UScalar.eq_of_val_eq h)
        simp [module.decode_table_type, hr, hv, core.result.Result.Insts.CoreOpsTry.branch]

namespace ModuleBinary

theorem At.rep_snoc {α : Type} {R : α → List U8 → Prop} {data start pos next xs x}
    (h : At (Rep R) data start xs pos) (h' : At R data pos x next) :
    At (Rep R) data start (xs ++ [x]) next := by
  obtain ⟨bytes, he, hs⟩ := h
  obtain ⟨last, he', hs'⟩ := h'
  exact ⟨bytes ++ last, he.snoc he', hs.append hs'⟩

end ModuleBinary

theorem module.decode_value_types_loop.spec (data : Slice U8) (start : Usize)
    (count : U32) (hb : start.val ≤ data.length) :
    module.decode_value_types_loop data count (alloc.vec.Vec.new types.ValueType) start 0#u32 ⦃ r =>
      match r with
      | .Ok (out, next) => At (Rep ValueTypeEncoding) data start out.val next ∧
          out.val.length = count.val
      | .Err _ => True ⦄ := by
  unfold module.decode_value_types_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ s.1.val.length = s.2.2.val ∧
      s.2.1.val = start.val + s.2.2.val ∧
      At (Rep ValueTypeEncoding) data start s.1.val s.2.1)
  · rintro ⟨out, pos, i⟩ ⟨hi, hlen, hpos, hrep⟩
    dsimp only at *
    by_cases hdone : count.val ≤ i.val
    · have he : i ≥ count := by scalar_tac
      simp [module.decode_value_types_loop.body, he]
      exact ⟨hrep, by omega⟩
    · have he : ¬i ≥ count := by scalar_tac
      obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (module.decode_value_type.spec data pos)
      cases r with
      | Err e =>
          simp [module.decode_value_types_loop.body, he, hr,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
          obtain ⟨ty, next⟩ := pair
          obtain ⟨bytes, hbytes, hs⟩ := hd
          have hbts : bytes = [valueByte ty] := hbytes
          subst bytes
          have hn : next.val = pos.val + 1 := by simpa using hs.length
          have hb' := hs.bound
          simp [module.decode_value_types_loop.body, he, hr,
            core.result.Result.Insts.CoreOpsTry.branch]
          step*
          refine ⟨by scalar_tac, ?_, by scalar_tac, ?_, by scalar_tac⟩
          · simp only [out1_post, List.length_append, List.length_singleton]
            scalar_tac
          · rw [out1_post]
            exact hrep.rep_snoc ⟨_, rfl, hs⟩
  · exact ⟨by scalar_tac, rfl, by simp, ⟨[], .nil, Wasm.BytesAt.nil data start hb⟩⟩

@[step]
theorem module.decode_value_types.spec (data : Slice U8) (start : Usize) :
    module.decode_value_types data start ⦃ r => match r with
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
      obtain ⟨r, hv, hp⟩ := WP.spec_imp_exists (module.decode_value_types_loop.spec data pos count hd.span.2.2)
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

@[step]
theorem module.decode_func_type.spec (data : Slice U8) (start : Usize) :
    module.decode_func_type data start ⦃ r => match r with
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

end Itasca
