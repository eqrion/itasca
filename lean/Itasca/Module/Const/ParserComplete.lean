import Itasca.Module.Const.Parser
import Itasca.Module.Readers.BasicComplete

open Aeneas Aeneas.Std

namespace Itasca

theorem module.expect_const_type.complete (ty : types.ValueType) :
    module.expect_const_type ty ty = .ok (.Ok ()) := by
  cases ty <;> simp [module.expect_const_type, core.cmp.PartialEq.ne.trait_default,
    core.cmp.PartialEq.ne.default, types.ValueType.Insts.CoreCmpPartialEqValueType.eq]

theorem module.read_expr_end.complete {data : Slice U8} {pos next : Usize}
    (h : Wasm1.BytesAt data pos [0x0B#u8] next) :
    module.read_expr_end data pos = .ok (.Ok next) := by
  simp [module.read_expr_end, h.read_byte, core.result.Result.Insts.CoreOpsTry.branch, global_simps]

theorem module.const_global.complete (env : module.Env) (idx : U32) (wanted : types.GlobalType)
    (hi : idx.val < env.global_types.val.length) (hgt : env.global_types.val[idx.val] = wanted)
    (hn : idx.val < env.num_imported_globals.val) (hm : wanted.mutability = .Const) :
    module.const_global env idx = .ok (.Ok wanted) := by
  have hs : module.const_global env idx ⦃ r => r = .Ok wanted ⦄ := by
    unfold module.const_global
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
          types.Mut.Insts.CoreCmpPartialEqMut.eq]
  obtain ⟨_, hr, rfl⟩ := WP.spec_imp_exists hs
  exact hr

/-- Every independently encoded valid initializer is accepted at its exact end. -/
theorem module.decode_const_expr.complete {data : Slice U8} {pos next : Usize}
    {env : module.Env} {expr : types.ConstExpr} {ty : types.ValueType}
    (hb : ModuleBinary.At ModuleBinary.ConstEncoding data pos expr next)
    (hv : ModuleConstants.Valid env expr ty) (profile : ValidationProfile)
    (hallowed : ModuleBinary.ConstAllowed profile expr) :
    module.decode_const_expr data pos env ty profile = .ok (.Ok (expr, next)) := by
  obtain ⟨bytes, he, hs⟩ := hb
  cases he with
  | @i32 value immediate hi =>
    cases hv
    obtain ⟨afterOp, hop, hrest⟩ := Wasm1.BytesAt.split
      (first := [0x41#u8]) (rest := immediate ++ [0x0B#u8]) hs
    obtain ⟨beforeEnd, himm, hend⟩ := hrest.split
    have hr := reader.read_s32_leb.complete data afterOp value beforeEnd
      ⟨immediate, himm.suffix, himm.length, himm.bound, hi⟩
    simp [module.decode_const_expr, hop.read_byte, hr, module.expect_const_type.complete,
      module.read_expr_end.complete hend, core.result.Result.Insts.CoreOpsTry.branch, global_simps]
  | @i64 value immediate hi =>
    cases hv
    obtain ⟨afterOp, hop, hrest⟩ := Wasm1.BytesAt.split
      (first := [0x42#u8]) (rest := immediate ++ [0x0B#u8]) hs
    obtain ⟨beforeEnd, himm, hend⟩ := hrest.split
    have hr := reader.read_s64_leb.complete data afterOp value beforeEnd
      ⟨immediate, himm.suffix, himm.length, himm.bound, hi⟩
    simp [module.decode_const_expr, hop.read_byte, hr, module.expect_const_type.complete,
      module.read_expr_end.complete hend, core.result.Result.Insts.CoreOpsTry.branch, global_simps]
  | @f32 value immediate hi =>
    cases hv
    obtain ⟨afterOp, hop, hrest⟩ := Wasm1.BytesAt.split
      (first := [0x43#u8]) (rest := immediate ++ [0x0B#u8]) hs
    obtain ⟨beforeEnd, himm, hend⟩ := hrest.split
    have hr := reader.read_f32_bits.complete data afterOp value beforeEnd
      ⟨immediate, himm.suffix, by simpa [hi.1] using himm.length, himm.bound, hi⟩
    simp [module.decode_const_expr, hop.read_byte, hr, module.expect_const_type.complete,
      module.read_expr_end.complete hend, core.result.Result.Insts.CoreOpsTry.branch, global_simps]
  | @f64 value immediate hi =>
    cases hv
    obtain ⟨afterOp, hop, hrest⟩ := Wasm1.BytesAt.split
      (first := [0x44#u8]) (rest := immediate ++ [0x0B#u8]) hs
    obtain ⟨beforeEnd, himm, hend⟩ := hrest.split
    have hr := reader.read_f64_bits.complete data afterOp value beforeEnd
      ⟨immediate, himm.suffix, by simpa [hi.1] using himm.length, himm.bound, hi⟩
    simp [module.decode_const_expr, hop.read_byte, hr, module.expect_const_type.complete,
      module.read_expr_end.complete hend, core.result.Result.Insts.CoreOpsTry.branch, global_simps]
  | @globalGet idx immediate hi =>
    cases hv with
    | globalGet _ gt hidx hgt hn hm =>
      obtain ⟨afterOp, hop, hrest⟩ := Wasm1.BytesAt.split
        (first := [0x23#u8]) (rest := immediate ++ [0x0B#u8]) hs
      obtain ⟨beforeEnd, himm, hend⟩ := hrest.split
      have hr := reader.read_u32_leb.complete data afterOp idx beforeEnd (himm.u32_decoded idx hi)
      have hg := module.const_global.complete env idx gt hidx hgt hn hm
      simp [module.decode_const_expr, hop.read_byte, hr, hg, module.expect_const_type.complete,
        module.read_expr_end.complete hend, core.result.Result.Insts.CoreOpsTry.branch, global_simps]

  | refNull refTy =>
    cases hv
    cases profile with
    | Wasm1 => exact hallowed.elim
    | Wasm2 =>
      obtain ⟨afterOp, hop, hrest⟩ := Wasm1.BytesAt.split
        (first := [0xD0#u8]) (rest := [ModuleBinary.elemByte refTy, 0x0B#u8]) hs
      obtain ⟨beforeEnd, himm, hend⟩ := Wasm1.BytesAt.split
        (first := [ModuleBinary.elemByte refTy]) (rest := [0x0B#u8]) hrest
      have hr := module.decode_elem_type.complete data afterOp refTy beforeEnd
        ⟨_, rfl, himm⟩ .Wasm2 (by cases refTy <;> trivial)
      have ht : types.ElemType.value_type refTy = .ok (ModuleConstants.referenceValueType refTy) := by
        cases refTy <;> rfl
      simp [module.decode_const_expr, hop.read_byte, hr, ht,
        module.expect_const_type.complete, module.read_expr_end.complete hend,
        core.result.Result.Insts.CoreOpsTry.branch]
  | @refFunc idx immediate hi =>
    cases hv with
    | refFunc _ hidx =>
      cases profile with
      | Wasm1 => exact hallowed.elim
      | Wasm2 =>
        obtain ⟨afterOp, hop, hrest⟩ := Wasm1.BytesAt.split
          (first := [0xD2#u8]) (rest := immediate ++ [0x0B#u8]) hs
        obtain ⟨beforeEnd, himm, hend⟩ := hrest.split
        have hr := reader.read_u32_leb.complete data afterOp idx beforeEnd (himm.u32_decoded idx hi)
        have hn : ¬idx.val ≥ env.func_types.val.length := by omega
        simp [module.decode_const_expr, hop.read_byte, hr, lift, hn,
          module.expect_const_type.complete, module.read_expr_end.complete hend,
          core.result.Result.Insts.CoreOpsTry.branch]
  | @v128 low high subBytes lowBytes highBytes hsub hlo hhi =>
    cases hv
    cases profile with
    | Wasm1 => exact hallowed.elim
    | Wasm2 =>
      obtain ⟨afterOp, hop, hrest⟩ := Wasm1.BytesAt.split
        (first := [0xFD#u8]) (rest := subBytes ++ lowBytes ++ highBytes ++ [0x0B#u8]) hs
      have hrest' : Wasm1.BytesAt data afterOp
          (subBytes ++ (lowBytes ++ (highBytes ++ [0x0B#u8]))) next := by
        simpa [List.append_assoc] using hrest
      obtain ⟨afterSub, hsubspan, hrest⟩ := hrest'.split
      obtain ⟨afterLow, hlospan, hrest⟩ := hrest.split
      obtain ⟨beforeEnd, hhispan, hend⟩ := hrest.split
      have hs := reader.read_u32_leb.complete data afterOp 12#u32 afterSub
        (hsubspan.u32_decoded 12#u32 hsub)
      have hl := reader.read_f64_bits.complete data afterSub low afterLow
        ⟨lowBytes, hlospan.suffix, by simpa [hlo.1] using hlospan.length, hlospan.bound, hlo⟩
      have hh := reader.read_f64_bits.complete data afterLow high beforeEnd
        ⟨highBytes, hhispan.suffix, by simpa [hhi.1] using hhispan.length, hhispan.bound, hhi⟩
      simp [module.decode_const_expr, hop.read_byte, hs, hl, hh,
        module.expect_const_type.complete, module.read_expr_end.complete hend,
        core.result.Result.Insts.CoreOpsTry.branch]

end Itasca
