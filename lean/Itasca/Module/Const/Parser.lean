import Itasca.Module.Const.Syntax
import Itasca.Module.Readers.Basic

/-!
# Constant expression parser

`metadata.decode_const_expr.spec` states that an accepted initializer is an exact `ConstEncoding`
span of the independent grammar and is `Valid` at the expected type. `allowed_spec` adds the
profile's `ConstAllowed` guard. The helpers `metadata.expect_const_type`, `metadata.const_global` and
`metadata.read_expr_end` have their own specs. Completeness is in `Module/Const/ParserComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- `metadata.expect_const_type` accepts exactly equal types and otherwise returns
`InvalidConstExpr`. -/
@[step]
theorem metadata.expect_const_type.spec (actual expected : wasm_types.ValueType) :
    metadata.expect_const_type actual expected ⦃ r =>
      match r with
      | .Ok _ => actual = expected
      | .Err e => e = .InvalidConstExpr ∧ actual ≠ expected ⦄ := by
  cases actual <;> cases expected <;>
    simp [metadata.expect_const_type, core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
      wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq]

/-- `metadata.const_global` returns the type of an in-range imported immutable global. -/
@[step]
theorem metadata.const_global.spec (env : metadata.Env) (idx : U32) :
    metadata.const_global env idx ⦃ r =>
      match r with
      | .Ok gt => ∃ hi : idx.val < env.global_types.val.length,
          env.global_types.val[idx.val] = gt ∧
          idx.val < env.num_imported_globals.val ∧ gt.mutability = .Const
      | .Err _ => True ⦄ := by
  unfold metadata.const_global
  step
  split
  · simp
  · split
    · simp
    · step
      rename_i gt hgt
      cases hm : gt.mutability <;>
        simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
          wasm_types.Mut.Insts.CoreCmpPartialEqMut.eq, hm]
      refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
      have hi : i.val = idx.val := by scalar_tac
      simpa [hi] using gt_post.symm

/-- An accepted `metadata.read_expr_end` consumed the single byte `0x0b`. -/
@[step]
theorem metadata.read_expr_end.spec (data : Slice U8) (pos : Usize) :
    metadata.read_expr_end data pos ⦃ r =>
      match r with
      | .Ok next => Wasm1.BytesAt data pos [0x0B#u8] next
      | .Err _ => True ⦄ := by
  unfold metadata.read_expr_end
  by_cases hb : pos.val < data.length
  · obtain ⟨_, hr, next, rfl, hp⟩ := WP.spec_imp_exists (reader.read_byte.spec data pos hb)
    by_cases he : data.val[pos.val] = 0x0B#u8
    · simpa [hr, core.result.Result.Insts.CoreOpsTry.branch, global_simps, he] using
        Wasm1.BytesAt.byte data pos next _ hb he hp
    · have hv : data.val[pos.val].val ≠ 11 := by scalar_tac
      simp [hr, core.result.Result.Insts.CoreOpsTry.branch, global_simps, hv]
  · simp [reader.read_byte.eof data pos (by omega),
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]

end Itasca

namespace Itasca.ModuleConstants

/-- The parser postcondition: an error carries no guarantee, and a success is a `ConstEncoding`
span whose expression is `Valid` at the expected type. -/
def Post (data : Slice U8) (pos : Usize) (env : metadata.Env)
    (expected : wasm_types.ValueType) :
    core.result.Result (wasm_types.ConstExpr × Usize) error.Error → Prop
  | .Err _ => True
  | .Ok (expr, next) => ModuleBinary.At ModuleBinary.ConstEncoding data pos expr next ∧
      Valid env expr expected

private theorem finish_spec (data : Slice U8) (start mid : Usize)
    (env : metadata.Env) (expected actual : wasm_types.ValueType) (expr : wasm_types.ConstExpr)
    (before : List U8) (hspan : Wasm1.BytesAt data start before mid)
    (hencoding : ModuleBinary.ConstEncoding expr (before ++ [0x0B#u8]))
    (hvalid : Valid env expr actual) :
    (do
      let r ← metadata.expect_const_type actual expected
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | .Continue _ =>
        let r ← metadata.read_expr_end data mid
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | .Continue next => .ok (core.result.Result.Ok (expr, next))
        | .Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (wasm_types.ConstExpr × Usize) (core.convert.FromSame error.Error) residual
      | .Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          (wasm_types.ConstExpr × Usize) (core.convert.FromSame error.Error) residual) ⦃ Post data start env expected ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (metadata.expect_const_type.spec actual expected)
  cases r with
  | Err e => simp [hr, Post, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok u =>
    dsimp only at hp
    subst expected
    obtain ⟨r, he, hp⟩ := WP.spec_imp_exists (metadata.read_expr_end.spec data mid)
    cases r with
    | Err e => simp [hr, he, Post, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok next =>
      simpa [hr, he, Post, core.result.Result.Insts.CoreOpsTry.branch] using
        And.intro (show ModuleBinary.At ModuleBinary.ConstEncoding data start expr next from
          ⟨_, hencoding, hspan.append hp⟩) hvalid

end Itasca.ModuleConstants

namespace Itasca

/-- `metadata.decode_const_expr` satisfies `ModuleConstants.Post`. -/
@[step]
theorem metadata.decode_const_expr.spec (data : Slice U8) (pos : Usize)
    (env : metadata.Env) (expected : wasm_types.ValueType) (profile : ValidationProfile) :
    metadata.decode_const_expr data pos env expected profile ⦃ ModuleConstants.Post data pos env expected ⦄ := by
  unfold metadata.decode_const_expr
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
        have himm : Wasm1.BytesAt data next bytes mid := ⟨hs, hl, hbound⟩
        have hs := (Wasm1.BytesAt.byte data pos next _ hb hop' hp).append himm
        have ht := ModuleConstants.finish_spec data pos mid env expected .I32
          (.I32 value) (0x41#u8 :: bytes) hs
          (by simpa using ModuleBinary.ConstEncoding.i32 value he)
          (ModuleConstants.Valid.i32 value)
        obtain ⟨typeResult, htype, _⟩ := WP.spec_imp_exists (metadata.expect_const_type.spec .I32 expected)
        obtain ⟨endResult, hend, _⟩ := WP.spec_imp_exists (metadata.read_expr_end.spec data mid)
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
        have himm : Wasm1.BytesAt data next bytes mid := ⟨hs, hl, hbound⟩
        have hs := (Wasm1.BytesAt.byte data pos next _ hb hop' hp).append himm
        have ht := ModuleConstants.finish_spec data pos mid env expected .I64
          (.I64 value) (0x42#u8 :: bytes) hs
          (by simpa using ModuleBinary.ConstEncoding.i64 value he)
          (ModuleConstants.Valid.i64 value)
        obtain ⟨typeResult, htype, _⟩ := WP.spec_imp_exists (metadata.expect_const_type.spec .I64 expected)
        obtain ⟨endResult, hend, _⟩ := WP.spec_imp_exists (metadata.read_expr_end.spec data mid)
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
        have himm : Wasm1.BytesAt data next bytes mid := ⟨hs, by rw [he.1]; exact hl, hbound⟩
        have hs := (Wasm1.BytesAt.byte data pos next _ hb hop' hp).append himm
        have ht := ModuleConstants.finish_spec data pos mid env expected .F32
          (.F32 value) (0x43#u8 :: bytes) hs
          (by simpa using ModuleBinary.ConstEncoding.f32 value he)
          (ModuleConstants.Valid.f32 value)
        obtain ⟨typeResult, htype, _⟩ := WP.spec_imp_exists (metadata.expect_const_type.spec .F32 expected)
        obtain ⟨endResult, hend, _⟩ := WP.spec_imp_exists (metadata.read_expr_end.spec data mid)
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
        have himm : Wasm1.BytesAt data next bytes mid := ⟨hs, by rw [he.1]; exact hl, hbound⟩
        have hs := (Wasm1.BytesAt.byte data pos next _ hb hop' hp).append himm
        have ht := ModuleConstants.finish_spec data pos mid env expected .F64
          (.F64 value) (0x44#u8 :: bytes) hs
          (by simpa using ModuleBinary.ConstEncoding.f64 value he)
          (ModuleConstants.Valid.f64 value)
        obtain ⟨typeResult, htype, _⟩ := WP.spec_imp_exists (metadata.expect_const_type.spec .F64 expected)
        obtain ⟨endResult, hend, _⟩ := WP.spec_imp_exists (metadata.read_expr_end.spec data mid)
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
        obtain ⟨r, hg, hglobal⟩ := WP.spec_imp_exists (metadata.const_global.spec env idx)
        cases r with
        | Err e =>
          simp [hd, hg,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            ModuleConstants.Post]
        | Ok gt =>
          obtain ⟨hi, hgt, himport, hconst⟩ := hglobal
          obtain ⟨bytes, hs, hl, hbound, he⟩ := hdecode
          have hop' : data.val[pos.val] = 0x23#u8 := by with_unfolding_all exact hop
          have himm : Wasm1.BytesAt data next bytes mid := ⟨hs, hl, hbound⟩
          have hs := (Wasm1.BytesAt.byte data pos next _ hb hop' hp).append himm
          have ht := ModuleConstants.finish_spec data pos mid env expected gt.valtype
            (.GlobalGet idx) (0x23#u8 :: bytes) hs
            (by simpa using ModuleBinary.ConstEncoding.globalGet idx he)
            (ModuleConstants.Valid.globalGet idx gt hi hgt himport hconst)
          obtain ⟨typeResult, htype, _⟩ := WP.spec_imp_exists (metadata.expect_const_type.spec gt.valtype expected)
          obtain ⟨endResult, hend, _⟩ := WP.spec_imp_exists (metadata.read_expr_end.spec data mid)
          cases typeResult <;> cases endResult <;>
          simpa [htype, hend, hd, hg, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame, bind_assoc] using ht
    · rename_i hop
      cases profile with
      | Wasm1 => simp [ModuleConstants.Post]
      | Wasm2 =>
        obtain ⟨r, hd, hdecode⟩ := WP.spec_imp_exists (metadata.decode_elem_type.spec data next .Wasm2)
        cases r with
        | Err e =>
          simp [hd, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            ModuleConstants.Post]
        | Ok pair =>
          obtain ⟨ty, mid⟩ := pair
          obtain ⟨bytes, ⟨rfl, _⟩, himm⟩ := hdecode
          have hop' : data.val[pos.val] = 0xD0#u8 := by with_unfolding_all exact hop
          have hs := (Wasm1.BytesAt.byte data pos next _ hb hop' hp).append himm
          have hv : wasm_types.ElemType.value_type ty = .ok (ModuleConstants.referenceValueType ty) := by
            cases ty <;> rfl
          have ht := ModuleConstants.finish_spec data pos mid env expected
            (ModuleConstants.referenceValueType ty) (.RefNull ty) [0xD0#u8, ModuleBinary.elemByte ty] hs
            (ModuleBinary.ConstEncoding.refNull ty) (ModuleConstants.Valid.refNull ty)
          obtain ⟨typeResult, htype, _⟩ := WP.spec_imp_exists
            (metadata.expect_const_type.spec (ModuleConstants.referenceValueType ty) expected)
          obtain ⟨endResult, hend, _⟩ := WP.spec_imp_exists (metadata.read_expr_end.spec data mid)
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
          simp [hd, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            error.Error.Insts.CoreConvertFromOpError.from, ModuleConstants.Post]
        | Ok pair =>
          obtain ⟨idx, mid⟩ := pair
          simp only [hd, bind_ok]
          step
          split
          · simp [ModuleConstants.Post]
          · have hi : idx.val < env.func_types.val.length := by scalar_tac
            obtain ⟨bytes, hsuffix, hlen, hbound, he⟩ := hdecode
            have hop' : data.val[pos.val] = 0xD2#u8 := by with_unfolding_all exact hop
            have himm : Wasm1.BytesAt data next bytes mid := ⟨hsuffix, hlen, hbound⟩
            have hs := (Wasm1.BytesAt.byte data pos next _ hb hop' hp).append himm
            have ht := ModuleConstants.finish_spec data pos mid env expected .FuncRef
              (.RefFunc idx) (0xD2#u8 :: bytes) hs
              (by simpa using ModuleBinary.ConstEncoding.refFunc idx he)
              (ModuleConstants.Valid.refFunc idx hi)
            obtain ⟨typeResult, htype, _⟩ := WP.spec_imp_exists (metadata.expect_const_type.spec .FuncRef expected)
            obtain ⟨endResult, hend, _⟩ := WP.spec_imp_exists (metadata.read_expr_end.spec data mid)
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
          simp [hsub, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            error.Error.Insts.CoreConvertFromOpError.from, ModuleConstants.Post]
        | Ok pair =>
          obtain ⟨sub, first⟩ := pair
          by_cases hcode : sub = 12#u32
          · subst sub
            obtain ⟨r, hlow, hlowdecode⟩ := WP.spec_imp_exists (reader.read_f64_bits.spec data first)
            cases r with
            | Err e =>
              simp [hsub, hlow,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                error.Error.Insts.CoreConvertFromOpError.from, ModuleConstants.Post]
            | Ok pair =>
              obtain ⟨low, second⟩ := pair
              obtain ⟨r, hhigh, hhighdecode⟩ := WP.spec_imp_exists (reader.read_f64_bits.spec data second)
              cases r with
              | Err e =>
                simp [hsub, hlow, hhigh,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                  error.Error.Insts.CoreConvertFromOpError.from, ModuleConstants.Post]
              | Ok pair =>
                obtain ⟨high, mid⟩ := pair
                obtain ⟨subbytes, hss, hsl, hsb, hse⟩ := hsubdecode
                obtain ⟨lowbytes, hls, hll, hlb, hle⟩ := hlowdecode
                obtain ⟨highbytes, hhs, hhl, hhb, hhe⟩ := hhighdecode
                have hs : Wasm1.BytesAt data next subbytes first := ⟨hss, hsl, hsb⟩
                have hl : Wasm1.BytesAt data first lowbytes second := ⟨hls, by rw [hle.1]; exact hll, hlb⟩
                have hh : Wasm1.BytesAt data second highbytes mid := ⟨hhs, by rw [hhe.1]; exact hhl, hhb⟩
                have hop' : data.val[pos.val] = 0xFD#u8 := by with_unfolding_all exact hop
                have hs := (((Wasm1.BytesAt.byte data pos next _ hb hop' hp).append hs).append hl).append hh
                have ht := ModuleConstants.finish_spec data pos mid env expected .V128
                  (.V128 low high) (0xFD#u8 :: (subbytes ++ lowbytes ++ highbytes))
                  (by simpa using hs)
                  (by simpa [List.append_assoc] using ModuleBinary.ConstEncoding.v128 low high hse hle hhe)
                  (ModuleConstants.Valid.v128 low high)
                obtain ⟨typeResult, htype, _⟩ := WP.spec_imp_exists (metadata.expect_const_type.spec .V128 expected)
                obtain ⟨endResult, hend, _⟩ := WP.spec_imp_exists (metadata.read_expr_end.spec data mid)
                cases typeResult <;> cases endResult <;>
                  simpa [hsub, hlow, hhigh, htype, hend, core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                    core.convert.FromSame, bind_assoc] using ht
          · have hcodeval : sub.val ≠ 12 := by
              intro he
              exact hcode (UScalar.eq_of_val_eq he)
            simp [hsub, hcodeval, ModuleConstants.Post]
    · simp [ModuleConstants.Post]
  · simp [reader.read_byte.eof data pos (by omega),
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from, ModuleConstants.Post]

end Itasca
