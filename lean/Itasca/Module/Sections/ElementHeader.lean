import Itasca.Module.Sections.ElementInit
import Itasca.Module.Readers.BasicComplete

open Aeneas Aeneas.Std

namespace Itasca.ModuleElements
open ModuleBinary

/-- A segment header records its byte grammar independently of validation. -/
inductive HeaderEncoding : ValidationProfile → module.ElementMode → types.ElemType → Bool → List U8 → Prop where
  | legacy {index offset ib ob} : IndexEncoding index ib → ConstEncoding offset ob →
      HeaderEncoding .Wasm1 (.Active index offset) .FuncRef false (ib ++ ob)
  | activeIndices {offset fb ob} : IndexEncoding 0#u32 fb → ConstEncoding offset ob →
      HeaderEncoding .Wasm2 (.Active 0#u32 offset) .FuncRef false (fb ++ ob)
  | passiveIndices {fb} : IndexEncoding 1#u32 fb →
      HeaderEncoding .Wasm2 .Passive .FuncRef false (fb ++ [0#u8])
  | explicitIndices {index offset fb ib ob} : IndexEncoding 2#u32 fb →
      IndexEncoding index ib → ConstEncoding offset ob →
      HeaderEncoding .Wasm2 (.Active index offset) .FuncRef false (fb ++ ib ++ ob ++ [0#u8])
  | declarativeIndices {fb} : IndexEncoding 3#u32 fb →
      HeaderEncoding .Wasm2 .Declarative .FuncRef false (fb ++ [0#u8])
  | activeExpressions {offset fb ob} : IndexEncoding 4#u32 fb → ConstEncoding offset ob →
      HeaderEncoding .Wasm2 (.Active 0#u32 offset) .FuncRef true (fb ++ ob)
  | passiveExpressions {elem fb} : IndexEncoding 5#u32 fb →
      HeaderEncoding .Wasm2 .Passive elem true (fb ++ [elemByte elem])
  | explicitExpressions {elem index offset fb ib ob} : IndexEncoding 6#u32 fb →
      IndexEncoding index ib → ConstEncoding offset ob →
      HeaderEncoding .Wasm2 (.Active index offset) elem true (fb ++ ib ++ ob ++ [elemByte elem])
  | declarativeExpressions {elem fb} : IndexEncoding 7#u32 fb →
      HeaderEncoding .Wasm2 .Declarative elem true (fb ++ [elemByte elem])

def HeaderValid (env : module.Env) (mode : module.ElementMode) (elem : types.ElemType) : Prop :=
  match mode with
  | .Active index offset => ∃ hi : index.val < env.table_types.val.length,
      env.table_types.val[index.val].elem = elem ∧ ModuleConstants.Valid env offset .I32
  | .Passive | .Declarative => True

private theorem indices_rep {values bytes}
    (h : Rep (InitializerEncoding false) values bytes) :
    ∃ indices, values = indices.map types.ConstExpr.RefFunc ∧ Rep IndexEncoding indices bytes := by
  induction h with
  | nil => exact ⟨[], rfl, .nil⟩
  | cons hv hs ih =>
    obtain ⟨index, rfl, hi⟩ := hv
    obtain ⟨indices, rfl, hrep⟩ := ih
    exact ⟨index :: indices, rfl, .cons hi hrep⟩

theorem indices_vector {values bytes}
    (h : VecEncoding (InitializerEncoding false) values bytes) :
    ∃ indices, values = indices.map types.ConstExpr.RefFunc ∧ VecEncoding IndexEncoding indices bytes := by
  obtain ⟨count, encoded, hc, hr, rfl⟩ := h
  obtain ⟨indices, rfl, hi⟩ := indices_rep hr
  exact ⟨indices, rfl, count, encoded, by simpa using hc, hi, rfl⟩

theorem HeaderEncoding.append {profile mode elem expressions header init bytes}
    (h : HeaderEncoding profile mode elem expressions header)
    (hi : VecEncoding (InitializerEncoding expressions) init bytes) :
    ElementEncodingFor profile ⟨elem, mode, init⟩ (header ++ bytes) := by
  cases h with
  | legacy hf ho =>
    obtain ⟨indices, rfl, hindices⟩ := indices_vector hi
    exact ⟨_, _, _, _, _, _, rfl, hf, ho, hindices, rfl⟩
  | activeIndices hf ho =>
    obtain ⟨indices, rfl, hindices⟩ := indices_vector hi
    exact .activeIndices hf ho hindices
  | passiveIndices hf =>
    obtain ⟨indices, rfl, hindices⟩ := indices_vector hi
    exact .passiveIndices hf hindices
  | explicitIndices hf ht ho =>
    obtain ⟨indices, rfl, hindices⟩ := indices_vector hi
    exact .explicitIndices hf ht ho hindices
  | declarativeIndices hf =>
    obtain ⟨indices, rfl, hindices⟩ := indices_vector hi
    exact .declarativeIndices hf hindices
  | activeExpressions hf ho => exact .activeExpressions hf ho hi
  | passiveExpressions hf => exact .passiveExpressions hf hi
  | explicitExpressions hf ht ho => exact .explicitExpressions hf ht ho hi
  | declarativeExpressions hf => exact .declarativeExpressions hf hi

theorem HeaderEncoding.initializer_type {profile mode elem expressions bytes}
    (h : HeaderEncoding profile mode elem expressions bytes) :
    initializerType elem expressions = ModuleConstants.referenceValueType elem := by
  cases h <;> rfl

theorem indices_vector_intro {indices bytes} (h : VecEncoding IndexEncoding indices bytes) :
    VecEncoding (InitializerEncoding false) (indices.map types.ConstExpr.RefFunc) bytes := by
  obtain ⟨count, encoded, hc, hr, rfl⟩ := h
  refine ⟨count, encoded, by simpa using hc, ?_, rfl⟩
  clear hc
  induction hr with
  | nil => exact .nil
  | cons hv hs ih => exact .cons ⟨_, rfl, hv⟩ ih

theorem header_parts {profile entry bytes} (h : ElementEncodingFor profile entry bytes) :
    ∃ expressions header encoded, HeaderEncoding profile entry.mode entry.elem expressions header ∧
      VecEncoding (InitializerEncoding expressions) entry.init encoded ∧ bytes = header ++ encoded := by
  cases profile with
  | Wasm1 =>
    obtain ⟨index, offset, initializers, ib, ob, entries, rfl, hi, ho, hv, rfl⟩ := h
    exact ⟨false, ib ++ ob, entries, .legacy hi ho, indices_vector_intro hv, rfl⟩
  | Wasm2 =>
    cases h with
    | activeIndices hf ho hi => exact ⟨false, _, _, .activeIndices hf ho, indices_vector_intro hi, rfl⟩
    | passiveIndices hf hi => exact ⟨false, _, _, .passiveIndices hf, indices_vector_intro hi, rfl⟩
    | explicitIndices hf ht ho hi => exact ⟨false, _, _, .explicitIndices hf ht ho, indices_vector_intro hi, rfl⟩
    | declarativeIndices hf hi => exact ⟨false, _, _, .declarativeIndices hf, indices_vector_intro hi, rfl⟩
    | activeExpressions hf ho hi => exact ⟨true, _, _, .activeExpressions hf ho, hi, rfl⟩
    | passiveExpressions hf hi => exact ⟨true, _, _, .passiveExpressions hf, hi, rfl⟩
    | explicitExpressions hf ht ho hi => exact ⟨true, _, _, .explicitExpressions hf ht ho, hi, rfl⟩
    | declarativeExpressions hf hi => exact ⟨true, _, _, .declarativeExpressions hf, hi, rfl⟩

theorem HeaderEncoding.const_allowed {profile mode elem expressions bytes}
    (h : HeaderEncoding profile mode elem expressions bytes) (value : types.ConstExpr)
    (he : expressions = true) : ConstAllowed profile value := by
  cases h <;> simp_all [ConstAllowed]

end Itasca.ModuleElements

namespace Itasca
open ModuleBinary ModuleElements

@[step]
theorem module.decode_element_header.spec (data : Slice U8) (pos : Usize)
    (env : module.Env) (profile : ValidationProfile) :
    module.decode_element_header data pos env profile ⦃ r => match r with
      | .Ok (mode, elem, expressions, next) =>
          At (fun value => HeaderEncoding profile value.1 value.2.1 value.2.2)
            data pos (mode, elem, expressions) next ∧ HeaderValid env mode elem
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e => simp [module.decode_element_header, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    obtain ⟨tag, first⟩ := pair
    obtain ⟨fb, hf, hfs⟩ := At.of_u32 hp
    simp only [module.decode_element_header, hr, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    cases profile with
    | Wasm1 =>
      dsimp only
      step
      split
      · simp
      · obtain ⟨r, hconst, hc⟩ := WP.spec_imp_exists
          (module.decode_const_expr.spec data first env .I32 .Wasm1)
        rw [hconst]
        cases r with
        | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok pair =>
          obtain ⟨offset, next⟩ := pair
          obtain ⟨⟨ob, ho, hos⟩, hv⟩ := hc
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          step
          split
          · simp
          · have hi : tag.val < env.table_types.val.length := by scalar_tac
            simp only [types.ElemType.value_type, bind_ok]
            step
            cases ht : tt.elem <;>
              simp [ht, types.ElemType.value_type, core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
                types.ValueType.Insts.CoreCmpPartialEqValueType,
                types.ValueType.Insts.CoreCmpPartialEqValueType.eq]
            exact ⟨⟨fb ++ ob, .legacy hf ho, hfs.append hos⟩,
              hi, (by
                have hrval : r.val = tag.val := by scalar_tac
                simpa [tt_post, hrval] using ht), hv⟩
    | Wasm2 =>
      change (if tag > 7#u32 then _ else _) ⦃_⦄
      by_cases htag : tag > 7#u32
      · rw [if_pos htag]
        simp
      · rw [if_neg htag]
        have hc : tag = 0#u32 ∨ tag = 1#u32 ∨ tag = 2#u32 ∨ tag = 3#u32 ∨
            tag = 4#u32 ∨ tag = 5#u32 ∨ tag = 6#u32 ∨ tag = 7#u32 := by scalar_tac
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals
          simp only [show (0#u32 % 2#u32 : Result U32) = .ok 0#u32 from by rfl,
            show (1#u32 % 2#u32 : Result U32) = .ok 1#u32 from by rfl,
            show (2#u32 % 2#u32 : Result U32) = .ok 0#u32 from by rfl,
            show (3#u32 % 2#u32 : Result U32) = .ok 1#u32 from by rfl,
            show (4#u32 % 2#u32 : Result U32) = .ok 0#u32 from by rfl,
            show (5#u32 % 2#u32 : Result U32) = .ok 1#u32 from by rfl,
            show (6#u32 % 2#u32 : Result U32) = .ok 0#u32 from by rfl,
            show (7#u32 % 2#u32 : Result U32) = .ok 1#u32 from by rfl, bind_ok]
          simp
        · step
          split
          · simp
          · obtain ⟨r, hconst, hc⟩ := WP.spec_imp_exists
              (module.decode_const_expr.spec data first env .I32 .Wasm2)
            rw [hconst]
            cases r with
            | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            error.Error.Insts.CoreConvertFromOpError.from]
            | Ok pair =>
              obtain ⟨offset, offsetNext⟩ := pair
              obtain ⟨⟨ob, ho, hos⟩, hv⟩ := hc
              simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
              step
              split
              · simp
              · have hi : (0#u32).val < env.table_types.val.length := by scalar_tac
                simp only [types.ElemType.value_type, bind_ok]
                step
                cases ht : tt.elem <;>
                  simp [types.ElemType.value_type, ModuleConstants.referenceValueType,
                    core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
                    types.ValueType.Insts.CoreCmpPartialEqValueType,
                    types.ValueType.Insts.CoreCmpPartialEqValueType.eq]
                all_goals
                  exact ⟨⟨fb ++ ob, .activeIndices hf ho, hfs.append hos⟩,
                    hi, (by
                      have hrval : r.val = (0#u32).val := by scalar_tac
                      simpa [tt_post, hrval] using ht), hv⟩
        · obtain ⟨r, hkind, hk⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data first)
          change (reader.read_byte data _ >>= _) ⦃_⦄
          rw [hkind]
          cases r with
          | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            error.Error.Insts.CoreConvertFromOpError.from]
          | Ok pair =>
            obtain ⟨kind, kindNext⟩ := pair
            by_cases hz : kind = 0#u8
            · subst kind
              have hks := At.byte hk
              simp [core.result.Result.Insts.CoreOpsTry.branch]
              exact ⟨⟨fb ++ [0#u8], .passiveIndices hf, hfs.append hks⟩, trivial⟩
            · have hn : kind.val ≠ 0 := fun h => hz (UScalar.eq_of_val_eq h)
              simp [core.result.Result.Insts.CoreOpsTry.branch, hn]
        · obtain ⟨r, hindex, hi⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data first)
          rw [hindex]
          cases r with
          | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            error.Error.Insts.CoreConvertFromOpError.from]
          | Ok pair =>
            obtain ⟨index, indexNext⟩ := pair
            obtain ⟨ib, hindexEnc, his⟩ := At.of_u32 hi
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            step
            split
            · simp
            · obtain ⟨r, hconst, hc⟩ := WP.spec_imp_exists
                (module.decode_const_expr.spec data indexNext env .I32 .Wasm2)
              rw [hconst]
              cases r with
              | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              error.Error.Insts.CoreConvertFromOpError.from]
              | Ok pair =>
                obtain ⟨offset, offsetNext⟩ := pair
                obtain ⟨⟨ob, ho, hos⟩, hv⟩ := hc
                simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
                obtain ⟨r, hkind, hk⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data offsetNext)
                change (reader.read_byte data _ >>= _) ⦃_⦄
                rw [hkind]
                cases r with
                | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                  error.Error.Insts.CoreConvertFromOpError.from]
                | Ok pair =>
                  obtain ⟨kind, kindNext⟩ := pair
                  by_cases hz : kind = 0#u8
                  · subst kind
                    have hks := At.byte hk
                    simp [core.result.Result.Insts.CoreOpsTry.branch]
                    step
                    split
                    · simp
                    · have hi : (index).val < env.table_types.val.length := by scalar_tac
                      simp only [types.ElemType.value_type, bind_ok]
                      step
                      cases ht : tt.elem <;>
                        simp [types.ElemType.value_type, ModuleConstants.referenceValueType,
                          core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
                          types.ValueType.Insts.CoreCmpPartialEqValueType,
                          types.ValueType.Insts.CoreCmpPartialEqValueType.eq]
                      all_goals
                        exact ⟨⟨fb ++ ib ++ ob ++ [0#u8], .explicitIndices hf hindexEnc ho, ((hfs.append his).append hos).append hks⟩,
                          hi, (by
                            have hentry : tt = env.table_types.val[index.val] := by
                              rw [tt_post]
                              congr 1 <;> scalar_tac
                            simpa [hentry] using ht), hv⟩
                  · have hn : kind.val ≠ 0 := fun h => hz (UScalar.eq_of_val_eq h)
                    simp [core.result.Result.Insts.CoreOpsTry.branch, hn]
        · obtain ⟨r, hkind, hk⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data first)
          change (reader.read_byte data _ >>= _) ⦃_⦄
          rw [hkind]
          cases r with
          | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            error.Error.Insts.CoreConvertFromOpError.from]
          | Ok pair =>
            obtain ⟨kind, kindNext⟩ := pair
            by_cases hz : kind = 0#u8
            · subst kind
              have hks := At.byte hk
              simp [core.result.Result.Insts.CoreOpsTry.branch]
              exact ⟨⟨fb ++ [0#u8], .declarativeIndices hf, hfs.append hks⟩, trivial⟩
            · have hn : kind.val ≠ 0 := fun h => hz (UScalar.eq_of_val_eq h)
              simp [core.result.Result.Insts.CoreOpsTry.branch, hn]
        · step
          split
          · simp
          · obtain ⟨r, hconst, hc⟩ := WP.spec_imp_exists
              (module.decode_const_expr.spec data first env .I32 .Wasm2)
            rw [hconst]
            cases r with
            | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            error.Error.Insts.CoreConvertFromOpError.from]
            | Ok pair =>
              obtain ⟨offset, offsetNext⟩ := pair
              obtain ⟨⟨ob, ho, hos⟩, hv⟩ := hc
              simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
              step
              split
              · simp
              · have hi : (0#u32).val < env.table_types.val.length := by scalar_tac
                simp only [types.ElemType.value_type, bind_ok]
                step
                cases ht : tt.elem <;>
                  simp [types.ElemType.value_type, ModuleConstants.referenceValueType,
                    core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
                    types.ValueType.Insts.CoreCmpPartialEqValueType,
                    types.ValueType.Insts.CoreCmpPartialEqValueType.eq]
                all_goals
                  exact ⟨⟨fb ++ ob, .activeExpressions hf ho, hfs.append hos⟩,
                    hi, (by
                      have hrval : r.val = (0#u32).val := by scalar_tac
                      simpa [tt_post, hrval] using ht), hv⟩
        · obtain ⟨r, helemRead, he⟩ := WP.spec_imp_exists (module.decode_elem_type.spec data first .Wasm2)
          simp only [helemRead, bind_ok]
          cases r with
          | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            error.Error.Insts.CoreConvertFromOpError.from]
          | Ok pair =>
            obtain ⟨elem, elemNext⟩ := pair
            obtain ⟨eb, ⟨he, ha⟩, hes⟩ := he
            have heq : eb = [elemByte elem] := he
            subst eb
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            exact ⟨⟨fb ++ [elemByte elem], .passiveExpressions hf, hfs.append hes⟩, trivial⟩
        · obtain ⟨r, hindex, hi⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data first)
          rw [hindex]
          cases r with
          | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            error.Error.Insts.CoreConvertFromOpError.from]
          | Ok pair =>
            obtain ⟨index, indexNext⟩ := pair
            obtain ⟨ib, hindexEnc, his⟩ := At.of_u32 hi
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            step
            split
            · simp
            · obtain ⟨r, hconst, hc⟩ := WP.spec_imp_exists
                (module.decode_const_expr.spec data indexNext env .I32 .Wasm2)
              rw [hconst]
              cases r with
              | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              error.Error.Insts.CoreConvertFromOpError.from]
              | Ok pair =>
                obtain ⟨offset, offsetNext⟩ := pair
                obtain ⟨⟨ob, ho, hos⟩, hv⟩ := hc
                simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
                let Target : WP.Post (core.result.Result (module.ElementMode × types.ElemType × Bool × Usize) error.Error) :=
                  fun result => match result with
                    | .Ok (mode, elem, expressions, next) =>
                        At (fun value => HeaderEncoding .Wasm2 value.1 value.2.1 value.2.2)
                          data pos (mode, elem, expressions) next ∧ HeaderValid env mode elem
                    | .Err _ => True
                change ((module.decode_elem_type data offsetNext .Wasm2 >>= _) :
                  Result (core.result.Result (module.ElementMode × types.ElemType × Bool × Usize) error.Error)) ⦃ Target ⦄
                obtain ⟨r, helemRead, he⟩ := WP.spec_imp_exists (module.decode_elem_type.spec data offsetNext .Wasm2)
                simp only [helemRead, bind_ok]
                cases r with
                | Err e => simp [Target, core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                  error.Error.Insts.CoreConvertFromOpError.from]
                | Ok pair =>
                  obtain ⟨elem, elemNext⟩ := pair
                  obtain ⟨eb, ⟨he, ha⟩, hes⟩ := he
                  have heq : eb = [elemByte elem] := he
                  subst eb
                  try with_unfolding_all simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
                  step
                  split
                  · simp [Target]
                  · have hi : (index).val < env.table_types.val.length := by scalar_tac
                    have hty : types.ElemType.value_type elem = .ok (ModuleConstants.referenceValueType elem) := by
                      cases elem <;> rfl
                    rw [hty]
                    simp only [bind_ok]
                    step
                    cases elem <;> cases ht : tt.elem <;>
                      simp [Target, types.ElemType.value_type, ModuleConstants.referenceValueType,
                        core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
                        types.ValueType.Insts.CoreCmpPartialEqValueType,
                        types.ValueType.Insts.CoreCmpPartialEqValueType.eq]
                    all_goals
                      exact ⟨⟨_, .explicitExpressions hf hindexEnc ho, ((hfs.append his).append hos).append hes⟩,
                        hi, (by
                          have hentry : tt = env.table_types.val[index.val] := by
                            rw [tt_post]
                            congr 1 <;> scalar_tac
                          simpa [hentry] using ht), hv⟩
        · obtain ⟨r, helemRead, he⟩ := WP.spec_imp_exists (module.decode_elem_type.spec data first .Wasm2)
          simp only [helemRead, bind_ok]
          cases r with
          | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            error.Error.Insts.CoreConvertFromOpError.from]
          | Ok pair =>
            obtain ⟨elem, elemNext⟩ := pair
            obtain ⟨eb, ⟨he, ha⟩, hes⟩ := he
            have heq : eb = [elemByte elem] := he
            subst eb
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            exact ⟨⟨fb ++ [elemByte elem], .declarativeExpressions hf, hfs.append hes⟩, trivial⟩

end Itasca

open Aeneas Aeneas.Std

namespace Itasca
open ModuleBinary ModuleElements

@[step]
theorem module.decode_element.spec (data : Slice U8) (pos : Usize)
    (env : module.Env) (profile : ValidationProfile)
    (hrefs : env.declared_funcs.val.length ≤ pos.val) :
    module.decode_element data pos env profile ⦃ r => match r.1 with
      | .Ok (entry, next) =>
          At (ElementEncodingFor profile) data pos ⟨entry.elem, entry.mode, entry.init.val⟩ next ∧
          ModuleReferences.Added env r.2 (ModuleReferences.element entry) ∧
          ModuleSegments.elementValid env entry ∧
          r.2.declared_funcs.val.length ≤ next.val ∧ pos.val < next.val
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (module.decode_element_header.spec data pos env profile)
  cases r with
  | Err e => simp [module.decode_element, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok tuple =>
    obtain ⟨mode, elem, expressions, middle⟩ := tuple
    obtain ⟨hheader, hvalid⟩ := hp
    have hspan := hheader.span
    obtain ⟨⟨r, result⟩, hinit, hp⟩ := WP.spec_imp_exists
      (module.decode_element_initializers.spec data middle env elem expressions profile (by omega))
    cases r with
    | Err e => simp [module.decode_element, hr, hinit, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok pair =>
      obtain ⟨init, next⟩ := pair
      obtain ⟨hib, hadded, hiv, hbound⟩ := hp
      simp [module.decode_element, hr, hinit, core.result.Result.Insts.CoreOpsTry.branch]
      obtain ⟨fb, hf, hfs⟩ := hheader
      have hty := hf.initializer_type
      have hprogress : middle.val < next.val := by
        obtain ⟨count, content, hn, hc, hi⟩ := hib.vector_split
        have := hc.span
        have := hi.span
        omega
      obtain ⟨ib, hi, his⟩ := hib
      exact ⟨⟨fb ++ ib, hf.append hi, hfs.append his⟩, hadded,
        ⟨hvalid, (by simpa only [hty] using hiv)⟩, hbound, by omega⟩

end Itasca
