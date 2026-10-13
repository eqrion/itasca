import Itasca.Module.Sections.ElementHeader
import Itasca.Module.Const.ParserComplete

open Aeneas Aeneas.Std

namespace Itasca
open ModuleBinary ModuleElements

theorem module.decode_element_header.complete {data : Slice U8} {pos next : Usize}
    {env : module.Env} {profile mode elem expressions}
    (hb : At (fun value => HeaderEncoding profile value.1 value.2.1 value.2.2)
      data pos (mode, elem, expressions) next)
    (hv : HeaderValid env mode elem) :
    module.decode_element_header data pos env profile = .ok (.Ok (mode, elem, expressions, next)) := by
  obtain ⟨bytes, he, hs⟩ := hb
  have hx : module.decode_element_header data pos env profile ⦃ r => r = .Ok (mode, elem, expressions, next) ⦄ := by
    cases he with
    | @legacy index offset fb ob hf ho =>
      obtain ⟨hi, ht, hv⟩ := hv
      obtain ⟨middle, hflags, hoffset⟩ := hs.split
      have hrf := hflags.read_u32 index hf
      have hro := module.decode_const_expr.complete (env := env) ⟨ob, ho, hoffset⟩ hv .Wasm1
        (hv.const_allowed (by trivial))
      simp [module.decode_element_header, hrf, hro, core.result.Result.Insts.CoreOpsTry.branch]
      step as ⟨cast1, hcast1⟩
      have hg1 : ¬env.table_types.val.length ≤ cast1.val := by scalar_tac
      simp only [hg1, ↓reduceIte]
      step as ⟨cast2, hcast2⟩
      have hg2 : ¬env.table_types.val.length ≤ cast2.val := by scalar_tac
      simp only [hg2, ↓reduceIte]
      have htype : types.ElemType.value_type types.ElemType.FuncRef = .ok (ModuleConstants.referenceValueType types.ElemType.FuncRef) := by rfl
      rw [htype]
      simp only [bind_ok]
      step as ⟨table, htable⟩
      have hte : table.elem = types.ElemType.FuncRef := by
        have hval : cast2.val = (index).val := by scalar_tac
        simpa only [htable, hval] using ht
      rw [hte]
      simp [ModuleConstants.referenceValueType, types.ElemType.value_type,
        core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
        types.ValueType.Insts.CoreCmpPartialEqValueType,
        types.ValueType.Insts.CoreCmpPartialEqValueType.eq]
    | @activeIndices offset fb ob hf ho =>
      obtain ⟨hi, ht, hv⟩ := hv
      obtain ⟨middle, hflags, hoffset⟩ := hs.split
      have hrf := hflags.read_u32 0#u32 hf
      have hro := module.decode_const_expr.complete (env := env) ⟨ob, ho, hoffset⟩ hv .Wasm2
        (hv.const_allowed (by trivial))
      simp [module.decode_element_header, hrf, hro, core.result.Result.Insts.CoreOpsTry.branch,
        show (0#u32 % 2#u32 : Result U32) = .ok 0#u32 from rfl]
      step as ⟨cast1, hcast1⟩
      have hg1 : ¬env.table_types.val.length ≤ cast1.val := by scalar_tac
      simp only [hg1, ↓reduceIte]
      step as ⟨cast2, hcast2⟩
      have hg2 : ¬env.table_types.val.length ≤ cast2.val := by scalar_tac
      simp only [hg2, ↓reduceIte]
      have htype : types.ElemType.value_type types.ElemType.FuncRef = .ok (ModuleConstants.referenceValueType types.ElemType.FuncRef) := by rfl
      rw [htype]
      simp only [bind_ok]
      step as ⟨table, htable⟩
      have hte : table.elem = types.ElemType.FuncRef := by
        have hval : cast2.val = (0#u32).val := by scalar_tac
        simpa only [htable, hval] using ht
      rw [hte]
      simp [ModuleConstants.referenceValueType, types.ElemType.value_type,
        core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
        types.ValueType.Insts.CoreCmpPartialEqValueType,
        types.ValueType.Insts.CoreCmpPartialEqValueType.eq]
    | @activeExpressions offset fb ob hf ho =>
      obtain ⟨hi, ht, hv⟩ := hv
      obtain ⟨middle, hflags, hoffset⟩ := hs.split
      have hrf := hflags.read_u32 4#u32 hf
      have hro := module.decode_const_expr.complete (env := env) ⟨ob, ho, hoffset⟩ hv .Wasm2
        (hv.const_allowed (by trivial))
      simp [module.decode_element_header, hrf, hro, core.result.Result.Insts.CoreOpsTry.branch,
        show (4#u32 % 2#u32 : Result U32) = .ok 0#u32 from rfl]
      step as ⟨cast1, hcast1⟩
      have hg1 : ¬env.table_types.val.length ≤ cast1.val := by scalar_tac
      simp only [hg1, ↓reduceIte]
      step as ⟨cast2, hcast2⟩
      have hg2 : ¬env.table_types.val.length ≤ cast2.val := by scalar_tac
      simp only [hg2, ↓reduceIte]
      have htype : types.ElemType.value_type types.ElemType.FuncRef = .ok (ModuleConstants.referenceValueType types.ElemType.FuncRef) := by rfl
      rw [htype]
      simp only [bind_ok]
      step as ⟨table, htable⟩
      have hte : table.elem = types.ElemType.FuncRef := by
        have hval : cast2.val = (0#u32).val := by scalar_tac
        simpa only [htable, hval] using ht
      rw [hte]
      simp [ModuleConstants.referenceValueType, types.ElemType.value_type,
        core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
        types.ValueType.Insts.CoreCmpPartialEqValueType,
        types.ValueType.Insts.CoreCmpPartialEqValueType.eq]
    | @passiveIndices fb hf =>
      obtain ⟨middle, hflags, hkind⟩ := hs.split
      have hrf := hflags.read_u32 1#u32 hf
      simp [module.decode_element_header, hrf, hkind.read_byte,
        show (1#u32 % 2#u32 : Result U32) = .ok 1#u32 from rfl,
        core.result.Result.Insts.CoreOpsTry.branch]
    | @declarativeIndices fb hf =>
      obtain ⟨middle, hflags, hkind⟩ := hs.split
      have hrf := hflags.read_u32 3#u32 hf
      simp [module.decode_element_header, hrf, hkind.read_byte,
        show (3#u32 % 2#u32 : Result U32) = .ok 1#u32 from rfl,
        core.result.Result.Insts.CoreOpsTry.branch]
    | @explicitIndices index offset fb ib ob hf hindexEnc ho =>
      obtain ⟨hi, ht, hv⟩ := hv
      obtain ⟨kindPos, hprefix, hkind⟩ := hs.split
      obtain ⟨offsetPos, hprefix, hoffset⟩ := hprefix.split
      obtain ⟨indexPos, hflags, hindex⟩ := hprefix.split
      have hrf := hflags.read_u32 2#u32 hf
      have hri := hindex.read_u32 index hindexEnc
      have hro := module.decode_const_expr.complete (env := env) ⟨ob, ho, hoffset⟩ hv .Wasm2 (by trivial)
      simp [module.decode_element_header, hrf, hri, hro, hkind.read_byte,
        show (2#u32 % 2#u32 : Result U32) = .ok 0#u32 from rfl,
        core.result.Result.Insts.CoreOpsTry.branch]
      step as ⟨cast1, hcast1⟩
      have hg1 : ¬env.table_types.val.length ≤ cast1.val := by scalar_tac
      simp only [hg1, ↓reduceIte]
      step as ⟨cast2, hcast2⟩
      have hg2 : ¬env.table_types.val.length ≤ cast2.val := by scalar_tac
      simp only [hg2, ↓reduceIte]
      have htype : types.ElemType.value_type types.ElemType.FuncRef = .ok (ModuleConstants.referenceValueType types.ElemType.FuncRef) := by rfl
      rw [htype]
      simp only [bind_ok]
      step as ⟨table, htable⟩
      have hte : table.elem = types.ElemType.FuncRef := by
        have hval : cast2.val = (index).val := by scalar_tac
        simpa only [htable, hval] using ht
      rw [hte]
      simp [ModuleConstants.referenceValueType, types.ElemType.value_type,
        core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
        types.ValueType.Insts.CoreCmpPartialEqValueType,
        types.ValueType.Insts.CoreCmpPartialEqValueType.eq]
    | @passiveExpressions elem fb hf =>
      obtain ⟨middle, hflags, helem⟩ := hs.split
      have hrf := hflags.read_u32 5#u32 hf
      have hre := module.decode_elem_type.complete data middle elem next ⟨_, rfl, helem⟩ .Wasm2 (by trivial)
      simp [module.decode_element_header, hrf, hre,
        show (5#u32 % 2#u32 : Result U32) = .ok 1#u32 from rfl,
        core.result.Result.Insts.CoreOpsTry.branch]
    | @declarativeExpressions elem fb hf =>
      obtain ⟨middle, hflags, helem⟩ := hs.split
      have hrf := hflags.read_u32 7#u32 hf
      have hre := module.decode_elem_type.complete data middle elem next ⟨_, rfl, helem⟩ .Wasm2 (by trivial)
      simp [module.decode_element_header, hrf, hre,
        show (7#u32 % 2#u32 : Result U32) = .ok 1#u32 from rfl,
        core.result.Result.Insts.CoreOpsTry.branch]
    | @explicitExpressions elem index offset fb ib ob hf hindexEnc ho =>
      obtain ⟨hi, ht, hv⟩ := hv
      obtain ⟨elemPos, hprefix, helem⟩ := hs.split
      obtain ⟨offsetPos, hprefix, hoffset⟩ := hprefix.split
      obtain ⟨indexPos, hflags, hindex⟩ := hprefix.split
      have hrf := hflags.read_u32 6#u32 hf
      have hri := hindex.read_u32 index hindexEnc
      have hro := module.decode_const_expr.complete (env := env) ⟨ob, ho, hoffset⟩ hv .Wasm2 (by trivial)
      have hre := module.decode_elem_type.complete data elemPos elem next ⟨_, rfl, helem⟩ .Wasm2 (by trivial)
      simp [module.decode_element_header, hrf, hri, hro, hre,
        show (6#u32 % 2#u32 : Result U32) = .ok 0#u32 from rfl,
        core.result.Result.Insts.CoreOpsTry.branch]
      step as ⟨cast1, hcast1⟩
      have hg1 : ¬env.table_types.val.length ≤ cast1.val := by scalar_tac
      simp only [hg1, ↓reduceIte]
      step as ⟨cast2, hcast2⟩
      have hg2 : ¬env.table_types.val.length ≤ cast2.val := by scalar_tac
      simp only [hg2, ↓reduceIte]
      have htype : types.ElemType.value_type elem = .ok (ModuleConstants.referenceValueType elem) := by cases elem <;> rfl
      rw [htype]
      simp only [bind_ok]
      step as ⟨table, htable⟩
      have hte : table.elem = elem := by
        have hval : cast2.val = (index).val := by scalar_tac
        simpa only [htable, hval] using ht
      rw [hte]
      cases elem <;> simp [ModuleConstants.referenceValueType, types.ElemType.value_type,
        core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
        types.ValueType.Insts.CoreCmpPartialEqValueType,
        types.ValueType.Insts.CoreCmpPartialEqValueType.eq]
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hx
  exact hr

end Itasca
