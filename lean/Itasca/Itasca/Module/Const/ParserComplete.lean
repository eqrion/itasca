import Itasca.Binary.ReaderBytes
import Itasca.Module.Elab.ToTyping
import Itasca.Module.Const.Parser
import Itasca.Module.Readers.Syntax

open WebAssembly

/-! ## Inversion -/

section

/-!
# Inversion of constant expression typing

Recovers `Module.Constants.Valid` from generated typing. `valid_of_typing` shows that a constant
initializer typed by `Expr_ok_const` is valid in the environment, including that `global.get`
targets an imported immutable global. Used by the completeness proofs for globals and segments.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Constants

/-- A constant, well-typed initializer instruction is valid at some type. -/
theorem constant_valid_type {env : metadata.Env} {C : context} {e : wasm_types.ConstExpr}
    (hg : GlobalContext env C) (hf : FunctionContext env C)
    (h : Instr_const C (instruction e))
    {ins outs : List valtype}
    (ht : Instr_ok C (instruction e) (.mk_functype (.mk_list ins) (.mk_list outs))) :
    ∃ ty, Valid env e ty := by
  change C.GLOBALS = (env.global_types.val.take env.num_imported_globals.val).map Translation.globalType at hg
  change C.FUNCS = env.func_types.val.map Translation.Environment.funcType at hf
  cases e with
  | I32 value => exact ⟨.I32, .i32 value⟩
  | I64 value => exact ⟨.I64, .i64 value⟩
  | F32 bits => exact ⟨.F32, .f32 bits⟩
  | F64 bits => exact ⟨.F64, .f64 bits⟩
  | V128 low high => exact ⟨.V128, .v128 low high⟩
  | RefNull ty => exact ⟨referenceValueType ty, .refNull ty⟩
  | RefFunc idx =>
    cases ht with
    | ref_func _ _ _ hi _ _ _ =>
      exact ⟨.FuncRef, .refFunc idx (by simpa [hf, proj_uN_0] using hi)⟩
  | GlobalGet idx =>
    cases h with
    | global_get _ t hi he hw hf =>
      have hbound : idx.val < (env.global_types.val.take env.num_imported_globals.val).length := by
        simpa [hg, proj_uN_0] using hi
      have hi' : idx.val < env.global_types.val.length := by simp only [List.length_take] at hbound; omega
      have hn : idx.val < env.num_imported_globals.val := by simp only [List.length_take] at hbound; omega
      let gt := env.global_types.val[idx.val]
      have hgt : Translation.globalType gt = .mk_globaltype none t := by
        change C.GLOBALS[idx.val]! = .mk_globaltype none t at he
        rw [hg, getElem!_pos _ _ (by simpa using hbound), List.getElem_map, List.getElem_take] at he
        exact he
      have hm : gt.mutability = .Const := by
        apply Translation.mutability_injective
        exact (globaltype.mk_globaltype.inj hgt).1
      exact ⟨gt.valtype, .globalGet idx gt hi' rfl hn hm⟩

/-- The output type of a typed initializer instruction is unique. -/
theorem instruction_output_unique {C : context} {e : wasm_types.ConstExpr} {ins outs ins' outs'}
    (h : Instr_ok C (instruction e) (.mk_functype (.mk_list ins) (.mk_list outs)))
    (h' : Instr_ok C (instruction e) (.mk_functype (.mk_list ins') (.mk_list outs'))) :
    outs = outs' := by
  cases e <;> cases h <;> cases h' <;> simp_all

/-- An initializer typed by `Expr_ok_const` at `Translation.valueType ty` satisfies `Valid env e
ty`. -/
theorem valid_of_typing {env : metadata.Env} {C : context} {e : wasm_types.ConstExpr} {ty : wasm_types.ValueType}
    (hg : GlobalContext env C) (hfunctions : FunctionContext env C) (h : Expr_ok_const C (expression e) (Translation.valueType ty)) :
    Valid env e ty := by
  cases h with
  | mk_Expr_ok_const ht hc hw hws =>
    have hconst : Instr_const C (instruction e) := by
      cases hc with
      | mk_Expr_const hc _ _ => exact hc _ (by simp [expression])
    have hseq : Instrs_ok C (expression e)
        (.mk_functype (.mk_list []) (.mk_list [Translation.valueType ty])) := by cases ht; assumption
    obtain ⟨front, ins, outs, hp, hi, ho⟩ := Spec.Completeness.singleton hseq
    obtain ⟨actual, hv⟩ := constant_valid_type hg hfunctions hconst hp
    have hcanonical := (hv.instruction_typed C hw hg hfunctions).1
    have hn := Spec.Completeness.result_sub_length hi
    have hf : front = [] := by
      apply List.length_eq_zero_iff.mp
      simp only [List.length_nil, List.length_append] at hn
      omega
    have hout := instruction_output_unique hp hcanonical
    rw [hf, List.nil_append, hout] at ho
    have hs := Spec.Completeness.result_sub_iff.mp ho
    have hsv : Valtype_sub (Translation.valueType actual) (Translation.valueType ty) := (List.forall₂_cons.mp hs).1
    have hnot : Translation.valueType actual ≠ .BOT := by cases actual <;> decide
    have sub_eq : ∀ {a b : valtype}, a ≠ .BOT → Valtype_sub a b → a = b := by
      intro a b hn ht
      cases ht with
      | refl => rfl
      | bot => exact False.elim (hn rfl)
    have he := Translation.value_type_injective (sub_eq hnot hsv)
    simpa [he] using hv

end Itasca.Module.Constants

end

/-! ## ParserComplete -/

section

/-!
# Completeness of the constant expression parser

`metadata.decode_const_expr.complete`: the parser accepts every independently encoded initializer
that is `Valid` at the expected type. The helpers
`metadata.expect_const_type`, `metadata.read_expr_end` and `metadata.const_global` have `.complete`
lemmas. Soundness is in `Module/Const/Parser`.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- `metadata.expect_const_type` accepts equal types. -/
theorem metadata.expect_const_type.complete (ty : wasm_types.ValueType) :
    metadata.expect_const_type ty ty = .ok (.Ok ()) := by
  cases ty <;> simp [metadata.expect_const_type, core.cmp.PartialEq.ne.trait_default,
    core.cmp.PartialEq.ne.default, wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq]

/-- `metadata.read_expr_end` accepts the byte `0x0b`. -/
theorem metadata.read_expr_end.complete {data : Slice U8} {pos next : Usize}
    (h : Body.Scalar.BytesAt data pos [0x0B#u8] next) :
    metadata.read_expr_end data pos = .ok (.Ok next) := by
  simp [metadata.read_expr_end, h.read_byte, core.result.Result.Insts.CoreOpsTry.branch, global_simps]

/-- `metadata.const_global` accepts an in-range imported immutable global. -/
theorem metadata.const_global.complete (env : metadata.Env) (idx : U32) (wanted : wasm_types.GlobalType)
    (hi : idx.val < env.global_types.val.length) (hgt : env.global_types.val[idx.val] = wanted)
    (hn : idx.val < env.num_imported_globals.val) (hm : wanted.mutability = .Const) :
    metadata.const_global env idx = .ok (.Ok wanted) := by
  have hs : metadata.const_global env idx ⦃ r => r = .Ok wanted ⦄ := by
    unfold metadata.const_global
    step
    split
    · scalar_tac
    · split
      · scalar_tac
      · step
        have he : gt = wanted := by
          have hx : gt = env.global_types.val[idx.val] := by
            simpa only [show i.val = idx.val by scalar_tac] using gt_post
          exact hx.trans hgt
        subst gt
        simp [he, hm, core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
          wasm_types.Mut.Insts.CoreCmpPartialEqMut.eq]
  obtain ⟨_, hr, rfl⟩ := WP.spec_imp_exists hs
  exact hr

/-- `metadata.decode_const_expr` accepts a valid `ConstEncoding` span and returns its end. -/
theorem metadata.decode_const_expr.complete {data : Slice U8} {pos next : Usize}
    {env : metadata.Env} {expr : wasm_types.ConstExpr} {ty : wasm_types.ValueType}
    (hb : Binary.At Binary.ConstEncoding data pos expr next)
    (hv : Module.Constants.Valid env expr ty) :
    metadata.decode_const_expr data pos env ty = .ok (.Ok (expr, next)) := by
  obtain ⟨bytes, he, hs⟩ := hb
  unfold Binary.ConstEncoding at he
  rw [← Binary.Source.readerBytes_bytes bytes] at hs
  generalize Binary.Source.bytes bytes = raw at he hs
  generalize hExpr : Binary.Source.constant expr = c at he
  cases he with
  | @i32 _ rawImm encoded =>
    obtain ⟨value, rfl, hi⟩ := Binary.Source.readerS32 encoded
    have eq : expr = .I32 value := Binary.Source.constantInjective hExpr
    subst expr
    let immediate := Binary.Source.readerBytes rawImm
    simp only [Binary.Source.readerBytes, List.map_cons, List.map_append, List.map_nil] at hs
    cases hv
    obtain ⟨afterOp, hop, hrest⟩ := Body.Scalar.BytesAt.split
      (first := [0x41#u8]) (rest := immediate ++ [0x0B#u8]) hs
    obtain ⟨beforeEnd, himm, hend⟩ := hrest.split
    have hr := reader.read_s32_leb.complete data afterOp value beforeEnd
      ⟨immediate, himm.suffix, himm.length, himm.bound, hi⟩
    simp [metadata.decode_const_expr, hop.read_byte, hr, metadata.expect_const_type.complete,
      metadata.read_expr_end.complete hend, core.result.Result.Insts.CoreOpsTry.branch, global_simps]
  | @i64 _ rawImm encoded =>
    obtain ⟨value, rfl, hi⟩ := Binary.Source.readerS64 encoded
    have eq : expr = .I64 value := Binary.Source.constantInjective hExpr
    subst expr
    let immediate := Binary.Source.readerBytes rawImm
    simp only [Binary.Source.readerBytes, List.map_cons, List.map_append, List.map_nil] at hs
    cases hv
    obtain ⟨afterOp, hop, hrest⟩ := Body.Scalar.BytesAt.split
      (first := [0x42#u8]) (rest := immediate ++ [0x0B#u8]) hs
    obtain ⟨beforeEnd, himm, hend⟩ := hrest.split
    have hr := reader.read_s64_leb.complete data afterOp value beforeEnd
      ⟨immediate, himm.suffix, himm.length, himm.bound, hi⟩
    simp [metadata.decode_const_expr, hop.read_byte, hr, metadata.expect_const_type.complete,
      metadata.read_expr_end.complete hend, core.result.Result.Insts.CoreOpsTry.branch, global_simps]
  | @f32 _ rawImm encoded =>
    obtain ⟨value, rfl, hi⟩ := Binary.Source.readerFloat32 encoded
    have eq : expr = .F32 value := Binary.Source.constantInjective hExpr
    subst expr
    let immediate := Binary.Source.readerBytes rawImm
    simp only [Binary.Source.readerBytes, List.map_cons, List.map_append, List.map_nil] at hs
    cases hv
    obtain ⟨afterOp, hop, hrest⟩ := Body.Scalar.BytesAt.split
      (first := [0x43#u8]) (rest := immediate ++ [0x0B#u8]) hs
    obtain ⟨beforeEnd, himm, hend⟩ := hrest.split
    have hr := reader.read_f32_bits.complete data afterOp value beforeEnd
      ⟨immediate, himm.suffix, himm.length.trans (congrArg (afterOp.val + ·) hi.1), himm.bound, hi⟩
    simp [metadata.decode_const_expr, hop.read_byte, hr, metadata.expect_const_type.complete,
      metadata.read_expr_end.complete hend, core.result.Result.Insts.CoreOpsTry.branch, global_simps]
  | @f64 _ rawImm encoded =>
    obtain ⟨value, rfl, hi⟩ := Binary.Source.readerFloat64 encoded
    have eq : expr = .F64 value := Binary.Source.constantInjective hExpr
    subst expr
    let immediate := Binary.Source.readerBytes rawImm
    simp only [Binary.Source.readerBytes, List.map_cons, List.map_append, List.map_nil] at hs
    cases hv
    obtain ⟨afterOp, hop, hrest⟩ := Body.Scalar.BytesAt.split
      (first := [0x44#u8]) (rest := immediate ++ [0x0B#u8]) hs
    obtain ⟨beforeEnd, himm, hend⟩ := hrest.split
    have hr := reader.read_f64_bits.complete data afterOp value beforeEnd
      ⟨immediate, himm.suffix, himm.length.trans (congrArg (afterOp.val + ·) hi.1), himm.bound, hi⟩
    simp [metadata.decode_const_expr, hop.read_byte, hr, metadata.expect_const_type.complete,
      metadata.read_expr_end.complete hend, core.result.Result.Insts.CoreOpsTry.branch, global_simps]
  | @globalGet _ rawImm encoded =>
    obtain ⟨idx, rfl, hi⟩ := Binary.Source.readerIndex encoded
    have eq : expr = .GlobalGet idx := Binary.Source.constantInjective hExpr
    subst expr
    let immediate := Binary.Source.readerBytes rawImm
    simp only [Binary.Source.readerBytes, List.map_cons, List.map_append, List.map_nil] at hs
    cases hv with
    | globalGet _ gt hidx hgt hn hm =>
      obtain ⟨afterOp, hop, hrest⟩ := Body.Scalar.BytesAt.split
        (first := [0x23#u8]) (rest := immediate ++ [0x0B#u8]) hs
      obtain ⟨beforeEnd, himm, hend⟩ := hrest.split
      have hr := reader.read_u32_leb.complete data afterOp idx beforeEnd (himm.u32_decoded idx hi)
      have hg := metadata.const_global.complete env idx gt hidx hgt hn hm
      simp [metadata.decode_const_expr, hop.read_byte, hr, hg, metadata.expect_const_type.complete,
        metadata.read_expr_end.complete hend, core.result.Result.Insts.CoreOpsTry.branch, global_simps]

  | refNull rt =>
    let refTy := Binary.Source.readerRef rt
    have eq : expr = .RefNull refTy := Binary.Source.constantInjective
      (by simpa only [Binary.Source.constant, refTy, Binary.Source.referenceType_readerRef] using hExpr)
    subst expr
    cases hv
    obtain ⟨afterOp, hop, hrest⟩ := Body.Scalar.BytesAt.split
      (first := [0xD0#u8]) (rest := [Binary.elemByte refTy, 0x0B#u8]) (by cases rt <;> exact hs)
    obtain ⟨beforeEnd, himm, hend⟩ := Body.Scalar.BytesAt.split
      (first := [Binary.elemByte refTy]) (rest := [0x0B#u8]) hrest
    have hr := metadata.decode_elem_type.complete data afterOp refTy beforeEnd
      ⟨_, rfl, himm⟩
    have ht : wasm_types.ElemType.value_type refTy = .ok (Module.Constants.referenceValueType refTy) := by
      cases refTy <;> rfl
    simp [metadata.decode_const_expr, hop.read_byte, hr, ht,
      metadata.expect_const_type.complete, metadata.read_expr_end.complete hend,
      core.result.Result.Insts.CoreOpsTry.branch]
  | @refFunc _ rawImm encoded =>
    obtain ⟨idx, rfl, hi⟩ := Binary.Source.readerIndex encoded
    have eq : expr = .RefFunc idx := Binary.Source.constantInjective hExpr
    subst expr
    let immediate := Binary.Source.readerBytes rawImm
    simp only [Binary.Source.readerBytes, List.map_cons, List.map_append, List.map_nil] at hs
    cases hv with
    | refFunc _ hidx =>
      obtain ⟨afterOp, hop, hrest⟩ := Body.Scalar.BytesAt.split
        (first := [0xD2#u8]) (rest := immediate ++ [0x0B#u8]) hs
      obtain ⟨beforeEnd, himm, hend⟩ := hrest.split
      have hr := reader.read_u32_leb.complete data afterOp idx beforeEnd (himm.u32_decoded idx hi)
      have hn : ¬idx.val ≥ env.func_types.val.length := by omega
      simp [metadata.decode_const_expr, hop.read_byte, hr, lift, hn,
        metadata.expect_const_type.complete, metadata.read_expr_end.complete hend,
        core.result.Result.Insts.CoreOpsTry.branch]
  | @v128 _ _ subRaw lowRaw highRaw subEnc lowEnc highEnc =>
    obtain ⟨low, rfl, hlo⟩ := Binary.Source.readerFloat64 lowEnc
    obtain ⟨high, rfl, hhi⟩ := Binary.Source.readerFloat64 highEnc
    have eq : expr = .V128 low high := Binary.Source.constantInjective hExpr
    subst expr
    let subBytes := Binary.Source.readerBytes subRaw
    let lowBytes := Binary.Source.readerBytes lowRaw
    let highBytes := Binary.Source.readerBytes highRaw
    have hsub := Binary.Source.readerLeb subEnc
    simp only [Binary.Source.readerBytes, List.map_cons, List.map_append, List.map_nil] at hs
    cases hv
    obtain ⟨afterOp, hop, hrest⟩ := Body.Scalar.BytesAt.split
      (first := [0xFD#u8]) (rest := subBytes ++ lowBytes ++ highBytes ++ [0x0B#u8]) hs
    have hrest' : Body.Scalar.BytesAt data afterOp
        (subBytes ++ (lowBytes ++ (highBytes ++ [0x0B#u8]))) next := by
      simpa [List.append_assoc] using hrest
    obtain ⟨afterSub, hsubspan, hrest⟩ := hrest'.split
    obtain ⟨afterLow, hlospan, hrest⟩ := hrest.split
    obtain ⟨beforeEnd, hhispan, hend⟩ := hrest.split
    have hs := reader.read_u32_leb.complete data afterOp 12#u32 afterSub
      (hsubspan.u32_decoded 12#u32 hsub)
    have hl := reader.read_f64_bits.complete data afterSub low afterLow
      ⟨lowBytes, hlospan.suffix, hlospan.length.trans (congrArg (afterSub.val + ·) hlo.1), hlospan.bound, hlo⟩
    have hh := reader.read_f64_bits.complete data afterLow high beforeEnd
      ⟨highBytes, hhispan.suffix, hhispan.length.trans (congrArg (afterLow.val + ·) hhi.1), hhispan.bound, hhi⟩
    simp [metadata.decode_const_expr, hop.read_byte, hs, hl, hh,
      metadata.expect_const_type.complete, metadata.read_expr_end.complete hend,
      core.result.Result.Insts.CoreOpsTry.branch]

end Itasca

end
