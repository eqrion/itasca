import Itasca.Module.Const.Syntax
import Itasca.Module.Readers.Basic

open Aeneas Aeneas.Std

namespace Itasca

@[step]
theorem module.expect_const_type.spec (actual expected : types.ValueType) :
    module.expect_const_type actual expected ⦃ r =>
      match r with
      | .Ok _ => actual = expected
      | .Err e => e = .InvalidConstExpr ∧ actual ≠ expected ⦄ := by
  cases actual <;> cases expected <;>
    simp [module.expect_const_type, core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
      types.ValueType.Insts.CoreCmpPartialEqValueType.eq]

@[step]
theorem module.const_global.spec (env : module.Env) (idx : U32) :
    module.const_global env idx ⦃ r =>
      match r with
      | .Ok gt => ∃ hi : idx.val < env.global_types.val.length,
          env.global_types.val[idx.val] = gt ∧
          idx.val < env.num_imported_globals.val ∧ gt.mutability = .Const
      | .Err _ => True ⦄ := by
  unfold module.const_global
  step
  split
  · simp
  · split
    · simp
    · step
      rename_i gt hgt
      cases hm : gt.mutability <;>
        simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
          types.Mut.Insts.CoreCmpPartialEqMut.eq, hm]
      refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
      have hi : i.val = idx.val := by scalar_tac
      simpa [hi] using gt_post.symm

@[step]
theorem module.read_expr_end.spec (data : Slice U8) (pos : Usize) :
    module.read_expr_end data pos ⦃ r =>
      match r with
      | .Ok next => Wasm.BytesAt data pos [0x0B#u8] next
      | .Err _ => True ⦄ := by
  unfold module.read_expr_end
  by_cases hb : pos.val < data.length
  · obtain ⟨_, hr, next, rfl, hp⟩ := WP.spec_imp_exists (reader.read_byte.spec data pos hb)
    by_cases he : data.val[pos.val] = 0x0B#u8
    · simpa [hr, core.result.Result.Insts.CoreOpsTry.branch, global_simps, he] using
        Wasm.BytesAt.byte data pos next _ hb he hp
    · have hv : data.val[pos.val].val ≠ 11 := by scalar_tac
      simp [hr, core.result.Result.Insts.CoreOpsTry.branch, global_simps, hv]
  · simp [reader.read_byte.eof data pos (by omega),
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]

end Itasca

namespace Itasca.ModuleConstants

def Post (data : Slice U8) (pos : Usize) (env : module.Env)
    (expected : types.ValueType) :
    core.result.Result (types.ConstExpr × Usize) error.Error → Prop
  | .Err _ => True
  | .Ok (expr, next) => ModuleBinary.At ModuleBinary.ConstEncoding data pos expr next ∧
      Valid env expr expected

private theorem finish_spec (data : Slice U8) (start mid : Usize)
    (env : module.Env) (expected actual : types.ValueType) (expr : types.ConstExpr)
    (before : List U8) (hspan : Wasm.BytesAt data start before mid)
    (hencoding : ModuleBinary.ConstEncoding expr (before ++ [0x0B#u8]))
    (hvalid : Valid env expr actual) :
    (do
      let r ← module.expect_const_type actual expected
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | .Continue _ =>
        let r ← module.read_expr_end data mid
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | .Continue next => .ok (core.result.Result.Ok (expr, next))
        | .Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (types.ConstExpr × Usize) (core.convert.FromSame error.Error) residual
      | .Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          (types.ConstExpr × Usize) (core.convert.FromSame error.Error) residual) ⦃ Post data start env expected ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (module.expect_const_type.spec actual expected)
  cases r with
  | Err e => simp [hr, Post, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok u =>
    dsimp only at hp
    subst expected
    obtain ⟨r, he, hp⟩ := WP.spec_imp_exists (module.read_expr_end.spec data mid)
    cases r with
    | Err e => simp [hr, he, Post, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok next =>
      simpa [hr, he, Post, core.result.Result.Insts.CoreOpsTry.branch] using
        And.intro (show ModuleBinary.At ModuleBinary.ConstEncoding data start expr next from
          ⟨_, hencoding, hspan.append hp⟩) hvalid

end Itasca.ModuleConstants

namespace Itasca

/-- Decoding proves an exact independent constant encoding and initializer validity. -/
@[step]
theorem module.decode_const_expr.spec (data : Slice U8) (pos : Usize)
    (env : module.Env) (expected : types.ValueType) (profile : ValidationProfile) :
    module.decode_const_expr data pos env expected profile ⦃ ModuleConstants.Post data pos env expected ⦄ := by
  unfold module.decode_const_expr
  by_cases hb : pos.val < data.length
  · obtain ⟨_, hr, next, rfl, hp⟩ := WP.spec_imp_exists (reader.read_byte.spec data pos hb)
    simp only [hr, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    change (match data.val[pos.val] with
      | 65#uscalar => _
      | 66#uscalar => _
      | 67#uscalar => _
      | 68#uscalar => _
      | 35#uscalar => _
      | 208#uscalar => _
      | 210#uscalar => _
      | 253#uscalar => _
      | _ => _) ⦃ _ ⦄
    split
    · rename_i hop
      obtain ⟨r, hd, hdecode⟩ := WP.spec_imp_exists (reader.read_s32_leb.spec data next)
      cases r with
      | Err e =>
        simp [hd,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          error.Error.Insts.CoreConvertFromOpError.from, ModuleConstants.Post]
      | Ok pair =>
        obtain ⟨value, mid⟩ := pair
        obtain ⟨bytes, hs, hl, hbound, he⟩ := hdecode
        have hop' : data.val[pos.val] = 0x41#u8 := by with_unfolding_all exact hop
        have himm : Wasm.BytesAt data next bytes mid := ⟨hs, hl, hbound⟩
        have hs := (Wasm.BytesAt.byte data pos next _ hb hop' hp).append himm
        have ht := ModuleConstants.finish_spec data pos mid env expected .I32
          (.I32 value) (0x41#u8 :: bytes) hs
          (by simpa using ModuleBinary.ConstEncoding.i32 value he)
          (ModuleConstants.Valid.i32 value)
        obtain ⟨typeResult, htype, _⟩ := WP.spec_imp_exists (module.expect_const_type.spec .I32 expected)
        obtain ⟨endResult, hend, _⟩ := WP.spec_imp_exists (module.read_expr_end.spec data mid)
        cases typeResult <;> cases endResult <;>
        simpa [htype, hend, hd, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame, bind_assoc] using ht
    · rename_i hop
      obtain ⟨r, hd, hdecode⟩ := WP.spec_imp_exists (reader.read_s64_leb.spec data next)
      cases r with
      | Err e =>
        simp [hd,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          error.Error.Insts.CoreConvertFromOpError.from, ModuleConstants.Post]
      | Ok pair =>
        obtain ⟨value, mid⟩ := pair
        obtain ⟨bytes, hs, hl, hbound, he⟩ := hdecode
        have hop' : data.val[pos.val] = 0x42#u8 := by with_unfolding_all exact hop
        have himm : Wasm.BytesAt data next bytes mid := ⟨hs, hl, hbound⟩
        have hs := (Wasm.BytesAt.byte data pos next _ hb hop' hp).append himm
        have ht := ModuleConstants.finish_spec data pos mid env expected .I64
          (.I64 value) (0x42#u8 :: bytes) hs
          (by simpa using ModuleBinary.ConstEncoding.i64 value he)
          (ModuleConstants.Valid.i64 value)
        obtain ⟨typeResult, htype, _⟩ := WP.spec_imp_exists (module.expect_const_type.spec .I64 expected)
        obtain ⟨endResult, hend, _⟩ := WP.spec_imp_exists (module.read_expr_end.spec data mid)
        cases typeResult <;> cases endResult <;>
        simpa [htype, hend, hd, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame, bind_assoc] using ht
    · rename_i hop
      obtain ⟨r, hd, hdecode⟩ := WP.spec_imp_exists (reader.read_f32_bits.spec data next)
      cases r with
      | Err e =>
        simp [hd,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          error.Error.Insts.CoreConvertFromOpError.from, ModuleConstants.Post]
      | Ok pair =>
        obtain ⟨value, mid⟩ := pair
        obtain ⟨bytes, hs, hl, hbound, he⟩ := hdecode
        have hop' : data.val[pos.val] = 0x43#u8 := by with_unfolding_all exact hop
        have himm : Wasm.BytesAt data next bytes mid := ⟨hs, by rw [he.1]; exact hl, hbound⟩
        have hs := (Wasm.BytesAt.byte data pos next _ hb hop' hp).append himm
        have ht := ModuleConstants.finish_spec data pos mid env expected .F32
          (.F32 value) (0x43#u8 :: bytes) hs
          (by simpa using ModuleBinary.ConstEncoding.f32 value he)
          (ModuleConstants.Valid.f32 value)
        obtain ⟨typeResult, htype, _⟩ := WP.spec_imp_exists (module.expect_const_type.spec .F32 expected)
        obtain ⟨endResult, hend, _⟩ := WP.spec_imp_exists (module.read_expr_end.spec data mid)
        cases typeResult <;> cases endResult <;>
        simpa [htype, hend, hd, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame, bind_assoc] using ht
    · rename_i hop
      obtain ⟨r, hd, hdecode⟩ := WP.spec_imp_exists (reader.read_f64_bits.spec data next)
      cases r with
      | Err e =>
        simp [hd,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          error.Error.Insts.CoreConvertFromOpError.from, ModuleConstants.Post]
      | Ok pair =>
        obtain ⟨value, mid⟩ := pair
        obtain ⟨bytes, hs, hl, hbound, he⟩ := hdecode
        have hop' : data.val[pos.val] = 0x44#u8 := by with_unfolding_all exact hop
        have himm : Wasm.BytesAt data next bytes mid := ⟨hs, by rw [he.1]; exact hl, hbound⟩
        have hs := (Wasm.BytesAt.byte data pos next _ hb hop' hp).append himm
        have ht := ModuleConstants.finish_spec data pos mid env expected .F64
          (.F64 value) (0x44#u8 :: bytes) hs
          (by simpa using ModuleBinary.ConstEncoding.f64 value he)
          (ModuleConstants.Valid.f64 value)
        obtain ⟨typeResult, htype, _⟩ := WP.spec_imp_exists (module.expect_const_type.spec .F64 expected)
        obtain ⟨endResult, hend, _⟩ := WP.spec_imp_exists (module.read_expr_end.spec data mid)
        cases typeResult <;> cases endResult <;>
        simpa [htype, hend, hd, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame, bind_assoc] using ht
    · rename_i hop
      obtain ⟨r, hd, hdecode⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data next)
      cases r with
      | Err e =>
        simp [hd,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          error.Error.Insts.CoreConvertFromOpError.from, ModuleConstants.Post]
      | Ok pair =>
        obtain ⟨idx, mid⟩ := pair
        obtain ⟨r, hg, hglobal⟩ := WP.spec_imp_exists (module.const_global.spec env idx)
        cases r with
        | Err e =>
          simp [hd, hg,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            ModuleConstants.Post]
        | Ok gt =>
          obtain ⟨hi, hgt, himport, hconst⟩ := hglobal
          obtain ⟨bytes, hs, hl, hbound, he⟩ := hdecode
          have hop' : data.val[pos.val] = 0x23#u8 := by with_unfolding_all exact hop
          have himm : Wasm.BytesAt data next bytes mid := ⟨hs, hl, hbound⟩
          have hs := (Wasm.BytesAt.byte data pos next _ hb hop' hp).append himm
          have ht := ModuleConstants.finish_spec data pos mid env expected gt.valtype
            (.GlobalGet idx) (0x23#u8 :: bytes) hs
            (by simpa using ModuleBinary.ConstEncoding.globalGet idx he)
            (ModuleConstants.Valid.globalGet idx gt hi hgt himport hconst)
          obtain ⟨typeResult, htype, _⟩ := WP.spec_imp_exists (module.expect_const_type.spec gt.valtype expected)
          obtain ⟨endResult, hend, _⟩ := WP.spec_imp_exists (module.read_expr_end.spec data mid)
          cases typeResult <;> cases endResult <;>
          simpa [htype, hend, hd, hg, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame, bind_assoc] using ht
    · rename_i hop
      cases profile with
      | Wasm1 => simp [ModuleConstants.Post]
      | Wasm2 =>
        obtain ⟨r, hd, hdecode⟩ := WP.spec_imp_exists (module.decode_elem_type.spec data next .Wasm2)
        cases r with
        | Err e =>
          simp [hd, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            ModuleConstants.Post]
        | Ok pair =>
          obtain ⟨ty, mid⟩ := pair
          obtain ⟨bytes, ⟨rfl, _⟩, himm⟩ := hdecode
          have hop' : data.val[pos.val] = 0xD0#u8 := by with_unfolding_all exact hop
          have hs := (Wasm.BytesAt.byte data pos next _ hb hop' hp).append himm
          have hv : types.ElemType.value_type ty = .ok (ModuleConstants.referenceValueType ty) := by
            cases ty <;> rfl
          have ht := ModuleConstants.finish_spec data pos mid env expected
            (ModuleConstants.referenceValueType ty) (.RefNull ty) [0xD0#u8, ModuleBinary.elemByte ty] hs
            (ModuleBinary.ConstEncoding.refNull ty) (ModuleConstants.Valid.refNull ty)
          obtain ⟨typeResult, htype, _⟩ := WP.spec_imp_exists
            (module.expect_const_type.spec (ModuleConstants.referenceValueType ty) expected)
          obtain ⟨endResult, hend, _⟩ := WP.spec_imp_exists (module.read_expr_end.spec data mid)
          cases typeResult <;> cases endResult <;>
            simpa [htype, hend, hd, hv, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              core.convert.FromSame, bind_assoc] using ht
    · rename_i hop
      cases profile with
      | Wasm1 => simp [ModuleConstants.Post]
      | Wasm2 =>
        obtain ⟨r, hd, hdecode⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data next)
        cases r with
        | Err e =>
          simp [hd, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            error.Error.Insts.CoreConvertFromOpError.from, ModuleConstants.Post]
        | Ok pair =>
          obtain ⟨idx, mid⟩ := pair
          simp only [hd, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
          step
          split
          · simp [ModuleConstants.Post]
          · have hi : idx.val < env.func_types.val.length := by scalar_tac
            obtain ⟨bytes, hsuffix, hlen, hbound, he⟩ := hdecode
            have hop' : data.val[pos.val] = 0xD2#u8 := by with_unfolding_all exact hop
            have himm : Wasm.BytesAt data next bytes mid := ⟨hsuffix, hlen, hbound⟩
            have hs := (Wasm.BytesAt.byte data pos next _ hb hop' hp).append himm
            have ht := ModuleConstants.finish_spec data pos mid env expected .FuncRef
              (.RefFunc idx) (0xD2#u8 :: bytes) hs
              (by simpa using ModuleBinary.ConstEncoding.refFunc idx he)
              (ModuleConstants.Valid.refFunc idx hi)
            obtain ⟨typeResult, htype, _⟩ := WP.spec_imp_exists (module.expect_const_type.spec .FuncRef expected)
            obtain ⟨endResult, hend, _⟩ := WP.spec_imp_exists (module.read_expr_end.spec data mid)
            cases typeResult <;> cases endResult <;>
              simpa [htype, hend, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                core.convert.FromSame, bind_assoc] using ht
    · rename_i hop
      cases profile with
      | Wasm1 => simp [ModuleConstants.Post]
      | Wasm2 =>
        obtain ⟨r, hsub, hsubdecode⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data next)
        cases r with
        | Err e =>
          simp [hsub, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            error.Error.Insts.CoreConvertFromOpError.from, ModuleConstants.Post]
        | Ok pair =>
          obtain ⟨sub, first⟩ := pair
          by_cases hcode : sub = 12#u32
          · subst sub
            obtain ⟨r, hlow, hlowdecode⟩ := WP.spec_imp_exists (reader.read_f64_bits.spec data first)
            cases r with
            | Err e =>
              simp [hsub, hlow, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                error.Error.Insts.CoreConvertFromOpError.from, ModuleConstants.Post]
            | Ok pair =>
              obtain ⟨low, second⟩ := pair
              obtain ⟨r, hhigh, hhighdecode⟩ := WP.spec_imp_exists (reader.read_f64_bits.spec data second)
              cases r with
              | Err e =>
                simp [hsub, hlow, hhigh, core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                  error.Error.Insts.CoreConvertFromOpError.from, ModuleConstants.Post]
              | Ok pair =>
                obtain ⟨high, mid⟩ := pair
                obtain ⟨subbytes, hss, hsl, hsb, hse⟩ := hsubdecode
                obtain ⟨lowbytes, hls, hll, hlb, hle⟩ := hlowdecode
                obtain ⟨highbytes, hhs, hhl, hhb, hhe⟩ := hhighdecode
                have hs : Wasm.BytesAt data next subbytes first := ⟨hss, hsl, hsb⟩
                have hl : Wasm.BytesAt data first lowbytes second := ⟨hls, by rw [hle.1]; exact hll, hlb⟩
                have hh : Wasm.BytesAt data second highbytes mid := ⟨hhs, by rw [hhe.1]; exact hhl, hhb⟩
                have hop' : data.val[pos.val] = 0xFD#u8 := by with_unfolding_all exact hop
                have hs := (((Wasm.BytesAt.byte data pos next _ hb hop' hp).append hs).append hl).append hh
                have ht := ModuleConstants.finish_spec data pos mid env expected .V128
                  (.V128 low high) (0xFD#u8 :: (subbytes ++ lowbytes ++ highbytes))
                  (by simpa using hs)
                  (by simpa [List.append_assoc] using ModuleBinary.ConstEncoding.v128 low high hse hle hhe)
                  (ModuleConstants.Valid.v128 low high)
                obtain ⟨typeResult, htype, _⟩ := WP.spec_imp_exists (module.expect_const_type.spec .V128 expected)
                obtain ⟨endResult, hend, _⟩ := WP.spec_imp_exists (module.read_expr_end.spec data mid)
                cases typeResult <;> cases endResult <;>
                  simpa [hsub, hlow, hhigh, htype, hend, core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                    core.convert.FromSame, bind_assoc] using ht
          · have hcodeval : sub.val ≠ 12 := by
              intro he
              exact hcode (UScalar.eq_of_val_eq he)
            simp [hsub, hcodeval, core.result.Result.Insts.CoreOpsTry.branch, ModuleConstants.Post]
    · simp [ModuleConstants.Post]
  · simp [reader.read_byte.eof data pos (by omega),
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from, ModuleConstants.Post]

private theorem module.decode_const_expr.allowed_only_spec (data : Slice U8) (pos : Usize)
    (env : module.Env) (expected : types.ValueType) (profile : ValidationProfile) :
    module.decode_const_expr data pos env expected profile ⦃ r => match r with
      | .Ok (expr, _) => ModuleBinary.ConstAllowed profile expr
      | .Err _ => True ⦄ := by
  cases profile with
  | Wasm2 =>
    apply WP.spec_mono (module.decode_const_expr.spec data pos env expected .Wasm2)
    intro r _
    cases r with
    | Err _ => trivial
    | Ok pair => cases pair.1 <;> trivial
  | Wasm1 =>
    obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data pos)
    cases r with
    | Err e => simp [module.decode_const_expr, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        error.Error.Insts.CoreConvertFromOpError.from]
    | Ok pair =>
      obtain ⟨op, next⟩ := pair
      simp only [module.decode_const_expr, hr, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      change (match op with
        | 65#uscalar => _
        | 66#uscalar => _
        | 67#uscalar => _
        | 68#uscalar => _
        | 35#uscalar => _
        | 208#uscalar => _
        | 210#uscalar => _
        | 253#uscalar => _
        | _ => _) ⦃ _ ⦄
      split <;> step*
      all_goals
        repeat' first
          | simp_all [ModuleBinary.ConstAllowed, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              error.Error.Insts.CoreConvertFromOpError.from]
          | step
          | split
      all_goals
        rename_i pair
        rcases pair with ⟨value, mid⟩
        repeat' first
          | simp_all [ModuleBinary.ConstAllowed, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              error.Error.Insts.CoreConvertFromOpError.from]
          | step
          | split

/-- The profile guards accompany exact bytes and generated initializer validity. -/
theorem module.decode_const_expr.allowed_spec (data : Slice U8) (pos : Usize)
    (env : module.Env) (expected : types.ValueType) (profile : ValidationProfile) :
    module.decode_const_expr data pos env expected profile ⦃ r =>
      ModuleConstants.Post data pos env expected r ∧
      (match r with
      | .Ok (expr, _) => ModuleBinary.ConstAllowed profile expr
      | .Err _ => True) ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (module.decode_const_expr.spec data pos env expected profile)
  obtain ⟨r', hr', ha⟩ := WP.spec_imp_exists
    (module.decode_const_expr.allowed_only_spec data pos env expected profile)
  have he : r' = r := by simpa only [Result.ok.injEq] using hr'.symm.trans hr
  subst r'
  simpa [hr] using And.intro hp ha

end Itasca
