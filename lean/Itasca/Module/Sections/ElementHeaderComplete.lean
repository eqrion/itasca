import Itasca.Module.Sections.ElementHeader
import Itasca.Module.Const.ParserComplete
import Itasca.Module.Sections.ElementInitComplete
import Itasca.Module.Env.Requirements

/-!
# Completeness of the element header and entry parser

`module.decode_element_header.complete` and `module.decode_element.complete`: an independently
encoded element header or entry that is valid in the environment is accepted, and the declared
functions gain its references. Soundness is in `Module/Sections/ElementHeader`.
-/

open Aeneas Aeneas.Std

namespace Itasca
open ModuleBinary ModuleElements

/-- `module.decode_element_header` accepts a valid `HeaderEncoding` span. -/
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
        types.ValueType.Insts.CoreCmpPartialEqValueType.eq]
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hx
  exact hr

end Itasca

open Aeneas Aeneas.Std

namespace Itasca
open ModuleBinary ModuleElements ModuleSections

/-- `module.decode_element` accepts an `ElementEncodingFor` span of a raw element that is valid in
the environment. -/
theorem module.decode_element.complete (data : Slice U8) (env : module.Env)
    (profile : ValidationProfile) (pos next : Usize) (entry : ModuleBinary.Element)
    (hb : At (ElementEncodingFor profile) data pos entry next)
    (hv : ElementValidRaw env entry) (hrefs : env.declared_funcs.val.length ≤ pos.val) :
    ∃ result actual, module.decode_element data pos env profile = .ok (.Ok (actual, next), result) ∧
      ModuleEnv.rawElement actual = entry ∧ ModuleReferences.Added env result (ModuleReferences.element actual) := by
  obtain ⟨bytes, he, hs⟩ := hb
  obtain ⟨expressions, header, encoded, hhead, hvalues, rfl⟩ := header_parts he
  obtain ⟨middle, hheader, hentries⟩ := hs.split
  have hreadheader := module.decode_element_header.complete (env := env)
    ⟨header, hhead, hheader⟩ hv.1
  have hspan := hheader.length
  have hty := hhead.initializer_type
  obtain ⟨result, init, hreadinit, hinit, hadded⟩ := module.decode_element_initializers.complete
    data env entry.elem expressions profile middle next entry.init ⟨encoded, hvalues, hentries⟩
    (by omega) (by simpa only [hty] using hv.2)
    (by intro value hm he; exact hhead.const_allowed value he)
  let actual : module.Element := ⟨entry.elem, entry.mode, init⟩
  refine ⟨result, actual, ?_, ?_, ?_⟩
  · simp [module.decode_element, hreadheader, hreadinit, actual,
      core.result.Result.Insts.CoreOpsTry.branch]
  · cases entry
    simp [ModuleEnv.rawElement, actual, hinit]
  · simpa only [ModuleReferences.element, actual, hinit] using hadded

end Itasca
