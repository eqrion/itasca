import Itasca.BodyContextComplete
import Itasca.ModuleProfile
import Itasca.ModuleTypingInversion

open Aeneas Aeneas.Std

namespace Itasca.CodeEntry

theorem function_body {C : context} {f ft} (h : Func_ok C f ft) :
    match f with
    | .FUNC _ locals body => ∃ declared params results,
        locals = declared.map _root_.local.LOCAL ∧
        ft = .mk_functype (.mk_list params) (.mk_list results) ∧
        Expr_ok ((⟨[], [], [], [], [], [], [], params ++ declared,
          [.mk_list results], some (.mk_list results)⟩ : context) ++ C)
          body (.mk_list results) := by
  cases h
  exact ⟨_, _, _, rfl, rfl, by assumption⟩

theorem Typed.of_func_ok {env : module.Env} {C : context} {idx : U32}
    {entry : ModuleBinary.Code} {ft : functype}
    (hc : ModuleContext env C) (hs : Forall BodyContext.SegmentFree entry.body)
    (hp : ModuleElaboration.FunctionProfile env.types.val idx entry)
    (hf : Func_ok C (function idx entry) ft) : Typed env idx entry := by
  have hi : idx.val < env.types.val.length := by
    simpa [function, hc.types, proj_uN_0] using ModuleElaboration.func_index_bound hf
  have hft := ModuleElaboration.function_type_of_typing hf hc.types
  rw [ModuleElaboration.functionType_lookup hi] at hft
  obtain ⟨declared, params, results, hd, ht, hb⟩ := function_body hf
  have hd' : entry.declared.map Translate.valueType = declared := by
    have he := congrArg (List.map (fun l => match l with | _root_.local.LOCAL t => t)) hd
    simpa [List.map_map, Function.comp_def] using he
  subst declared
  rw [ht] at hft
  simp only [EnvTranslation.funcType, functype.mk_functype.injEq, list.mk_list.injEq] at hft
  obtain ⟨rfl, rfl⟩ := hft
  let ftype := env.types.val[idx.val]'hi
  have hcore : BodyContext.SameCore
      ((⟨[], [], [], [], [], [], [],
          ftype.params.val.map Translate.valueType ++ entry.declared.map Translate.valueType,
          [.mk_list (ftype.results.val.map Translate.valueType)],
          some (.mk_list (ftype.results.val.map Translate.valueType))⟩ : context) ++ C)
      (bodyContext env ftype.params.val entry.declared ftype.results.val) := by
    constructor
    · exact hc.types
    · exact hc.funcs
    · exact hc.globals
    · exact hc.tables
    · exact hc.mems
    · change (ftype.params.val.map Translate.valueType ++ entry.declared.map Translate.valueType) ++ C.LOCALS = _
      simp [bodyContext, hc.locals]
    · change [.mk_list (ftype.results.val.map Translate.valueType)] ++ C.LABELS = _
      simp [bodyContext, hc.labels]
    · rfl
  cases hb with
  | mk_Expr_ok ts hbody hw hws =>
    refine ⟨hi, BodyContext.instrs_transport_of_syntax hbody hs hcore, ?_⟩
    exact hp.choose_spec.congr_labels _ rfl

end Itasca.CodeEntry
