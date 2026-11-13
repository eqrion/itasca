import Itasca.Binary.UnicodeUnique
import Itasca.Module.Elab.Translation
import Itasca.Module.Readers.Types

/-!
Sections, each formerly its own module: Syntax, Typing, Parser.
-/

/-! ## Syntax -/

section

/-!
# Constant expression syntax

`ModuleConstants.Valid` is the validator's typing relation for constant initializers
(`wasm_types.ConstExpr`), independent of parsing. `instruction` and `expression` translate an
initializer to SpecTec syntax, and `GlobalContext` and `FunctionContext` tie a SpecTec `context`
to the decoded environment. Typing against `Expr_ok_const` is in `Module/Const/Typing`.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleConstants

/-- The operand type corresponding to a table element type. -/
def referenceValueType : wasm_types.ElemType → wasm_types.ValueType
  | .FuncRef => .FuncRef
  | .ExternRef => .ExternRef

/-- The initializer has the given type in `env`. `ref.func` needs an in-range function index, and
`global.get` needs an imported immutable global. -/
inductive Valid (env : metadata.Env) : wasm_types.ConstExpr → wasm_types.ValueType → Prop where
  | i32 (value : I32) : Valid env (.I32 value) .I32
  | i64 (value : I64) : Valid env (.I64 value) .I64
  | f32 (value : U32) : Valid env (.F32 value) .F32
  | f64 (value : U64) : Valid env (.F64 value) .F64
  | v128 (low high : U64) : Valid env (.V128 low high) .V128
  | refNull (ty : wasm_types.ElemType) : Valid env (.RefNull ty) (referenceValueType ty)
  | refFunc (idx : U32) (hi : idx.val < env.func_types.val.length) :
      Valid env (.RefFunc idx) .FuncRef
  | globalGet (idx : U32) (gt : wasm_types.GlobalType)
      (hi : idx.val < env.global_types.val.length)
      (hgt : env.global_types.val[idx.val] = gt)
      (himport : idx.val < env.num_imported_globals.val)
      (hconst : gt.mutability = .Const) : Valid env (.GlobalGet idx) gt.valtype

/-- Translates an initializer to a SpecTec instruction. `V128` combines the low and high halves in
little-endian order. -/
def instruction : wasm_types.ConstExpr → instr
  | .I32 value => Spec.i32Const value
  | .I64 value => ScalarConst.i64 value
  | .F32 bits => ScalarConst.f32 bits
  | .F64 bits => ScalarConst.f64 bits
  | .V128 low high => .VCONST .V128 (.mk_uN (low.val + high.val * 2 ^ 64))
  | .RefNull ty => .REF_NULL (Translate.referenceType ty)
  | .RefFunc idx => .REF_FUNC (.mk_uN idx.val)
  | .GlobalGet idx => .GLOBAL_GET (.mk_uN idx.val)

/-- The single-instruction SpecTec expression of an initializer. -/
def expression (e : wasm_types.ConstExpr) : expr := [instruction e]

/-- The translated instruction is well-formed. -/
theorem instruction_wf (e : wasm_types.ConstExpr) : wf_instr (instruction e) := by
  cases e with
  | I32 value => exact Spec.i32Const_wf value
  | I64 value => exact ScalarConst.i64_wf value
  | F32 value => exact ScalarConst.f32_wf value
  | F64 value => exact ScalarConst.f64_wf value
  | V128 low high =>
    apply wf_instr.instr_case_20
    · decide
    · constructor
      have hlo : low.val ≤ 18446744073709551615 := by scalar_tac
      have hhi : high.val ≤ 18446744073709551615 := by scalar_tac
      norm_num [size, valtype_vectype]
      omega
  | RefNull _ => exact .instr_case_40 _
  | RefFunc idx => exact .instr_case_41 _ (EnvTranslation.index_wf idx)
  | GlobalGet idx => exact .instr_case_46 _ (EnvTranslation.index_wf idx)

theorem expression_wf (e : wasm_types.ConstExpr) : Forall wf_instr (expression e) := by
  simpa [expression, Forall] using instruction_wf e

/-- `C.GLOBALS` is the imported prefix of the environment's global types. -/
def GlobalContext (env : metadata.Env) (C : context) : Prop :=
  C.GLOBALS = (env.global_types.val.take env.num_imported_globals.val).map Translate.globalType

/-- `C.FUNCS` is the environment's function types, imported and defined. -/
def FunctionContext (env : metadata.Env) (C : context) : Prop :=
  C.FUNCS = env.func_types.val.map EnvTranslation.funcType

end Itasca.ModuleConstants

end

/-! ## Typing -/

section

/-!
# Typing of constant expressions

A valid initializer is generated-typed: `Valid.instruction_typed` gives `Instr_ok` and
`Instr_const`, `Valid.expr_ok_const` gives `Expr_ok_const`, and `global_typed` gives `Global_ok`
for a global with a valid initializer. The converse is in `Module/Const/Inversion`.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleConstants

private theorem global_lookup {env C} (hC : GlobalContext env C)
    (idx : U32) (gt : wasm_types.GlobalType) (hi : idx.val < env.global_types.val.length)
    (hgt : env.global_types.val[idx.val] = gt) (himport : idx.val < env.num_imported_globals.val) :
    idx.val < C.GLOBALS.length ∧ C.GLOBALS[idx.val]! = Translate.globalType gt := by
  rw [hC]
  have hb : idx.val < (env.global_types.val.take env.num_imported_globals.val).length := by simp; omega
  exact ⟨by simpa using hb, by
    rw [getElem!_pos _ _ (by simpa using hb), List.getElem_map, List.getElem_take, hgt]⟩

/-- A valid initializer is a constant instruction typed `[] -> [t]` under any context that agrees
with the environment. -/
theorem Valid.instruction_typed {env e t} (h : Valid env e t)
    (C : context) (hC : wf_context C) (hglobals : GlobalContext env C) (hfunctions : FunctionContext env C) :
    Instr_ok C (instruction e) (.mk_functype (.mk_list []) (.mk_list [Translate.valueType t])) ∧
      Instr_const C (instruction e) := by
  cases h with
  | i32 value => exact ⟨Spec.i32Const_typed C hC value, .const C _ _ hC (instruction_wf (.I32 value))⟩
  | i64 value => exact ⟨ScalarConst.i64_typed C hC value, .const C _ _ hC (instruction_wf (.I64 value))⟩
  | f32 value => exact ⟨ScalarConst.f32_typed C hC value, .const C _ _ hC (instruction_wf (.F32 value))⟩
  | f64 value => exact ⟨ScalarConst.f64_typed C hC value, .const C _ _ hC (instruction_wf (.F64 value))⟩
  | v128 low high =>
    exact ⟨.vconst C _ hC (instruction_wf (.V128 low high)), .vconst C _ _ hC (instruction_wf (.V128 low high))⟩
  | refNull ty =>
    have hv : valtype_reftype (Translate.referenceType ty) = Translate.valueType (referenceValueType ty) := by
      cases ty <;> rfl
    exact ⟨hv ▸ Instr_ok.ref_null C _ hC (instruction_wf (.RefNull ty)), .ref_null C _ hC (instruction_wf (.RefNull ty))⟩
  | refFunc idx hi =>
    have hb : idx.val < C.FUNCS.length := by rw [hfunctions, List.length_map]; exact hi
    exact ⟨.ref_func C (.mk_uN idx.val) C.FUNCS[idx.val]! hb rfl hC (instruction_wf (.RefFunc idx)),
      .ref_func C (.mk_uN idx.val) hC (instruction_wf (.RefFunc idx))⟩
  | globalGet idx gt hi hgt himport hconst =>
    obtain ⟨hb, he⟩ := global_lookup hglobals idx gt hi hgt himport
    refine ⟨.global_get C _ _ (Translate.mutability gt.mutability) hb he hC (instruction_wf (.GlobalGet idx)), ?_⟩
    apply Instr_const.global_get C _ (Translate.valueType gt.valtype) hb _ hC
      (instruction_wf (.GlobalGet idx))
    simpa [Translate.globalType, hconst, Translate.mutability, proj_uN_0] using he

/-- A valid initializer satisfies `Expr_ok_const` at its type. -/
theorem Valid.expr_ok_const {env e t} (h : Valid env e t)
    (C : context) (hC : wf_context C) (hglobals : GlobalContext env C) (hfunctions : FunctionContext env C) :
    Expr_ok_const C (expression e) (Translate.valueType t) := by
  obtain ⟨ht, hc⟩ := h.instruction_typed C hC hglobals hfunctions
  exact .mk_Expr_ok_const C _ _
    (.mk_Expr_ok C _ _ (.instr C _ [] _ ht hC (instruction_wf _)) hC (expression_wf _))
    (.mk_Expr_const C _ (by simpa [Forall, expression] using hc) hC (expression_wf _))
    hC (expression_wf _)

/-- The SpecTec global of a decoded global. -/
def global (g : metadata.Global) : _root_.global :=
  .GLOBAL (Translate.globalType g.gtype) (expression g.init)

/-- A global with a valid initializer satisfies `Global_ok`. -/
theorem global_typed (env : metadata.Env) (g : metadata.Global)
    (h : Valid env g.init g.gtype.valtype) (C : context)
    (hC : wf_context C) (hglobals : GlobalContext env C) (hfunctions : FunctionContext env C) :
    Global_ok C (global g) (Translate.globalType g.gtype) := by
  apply Global_ok.mk_Global_ok C _ _ (Translate.mutability g.gtype.mutability)
      (Translate.valueType g.gtype.valtype)
  · exact Translate.globalType_valid _
  · rfl
  · exact h.expr_ok_const C hC hglobals hfunctions
  · exact hC
  · exact .global_case_0 _ _ (expression_wf _)

end Itasca.ModuleConstants

end

/-! ## Parser -/

section

/-!
# Constant expression parser

`metadata.decode_const_expr.spec` states that an accepted initializer is an exact `ConstEncoding`
span of the independent grammar and is `Valid` at the expected type. The helpers `metadata.expect_const_type`, `metadata.const_global` and
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
    (env : metadata.Env) (expected : wasm_types.ValueType) :
    metadata.decode_const_expr data pos env expected ⦃ ModuleConstants.Post data pos env expected ⦄ := by
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
      obtain ⟨r, hd, hdecode⟩ := WP.spec_imp_exists (metadata.decode_elem_type.spec data next)
      cases r with
      | Err e =>
        simp [hd, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          ModuleConstants.Post]
      | Ok pair =>
        obtain ⟨ty, mid⟩ := pair
        obtain ⟨bytes, rfl, himm⟩ := hdecode
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

end
