import Itasca.Module.Env.Requirements
import Itasca.CodeEntry.Validation
import Itasca.Module.Code.ContextTransport
import Itasca.Module.Elab.ToTyping

/-! ## EntryOfEnv -/

section

/-!
# Code entry validation under an accepted environment

`Module.Environment.accepted_entry_conditions` derives entry allocation bounds and
signature limits from successful environment parsing on bounded input. The
following section relates generated function typing to `CodeEntry.Typed`,
using explicit module-context and declared-reference premises.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Environment

/-- An accepted environment decoded from input within the size limit supplies the entry
prerequisites for the instruction grammar: the allocation bound and signatures within the
completeness limits. -/
theorem accepted_entry_conditions (data : Slice U8) (env : metadata.Env) (next : Usize)
     (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (h : metadata.validate_env data = .ok (.Ok (env, next))) :
    CodeEntry.Bounds env ∧ CodeEntry.EnvironmentWithinLimits env := by
  have hs := metadata.validate_env.semantic_spec data
  rw [h] at hs
  simp only [WP.spec_ok] at hs
  obtain ⟨decls, hr, hv, hsig, _, hb⟩ := hs
  exact ⟨CodeEntry.Bounds.of_module_bound env (hsig.mono (by have := hb.span.2; omega)),
    hv.environment_within_limits hr.cache⟩

end Itasca.Module.Environment

end

/-! ## FuncTyping -/

section

/-!
# Code entry typing from function typing

The converse of `CodeEntry.typed_func_ok`. `function_body` inverts the generated `Func_ok`, and
`Typed.of_func_ok` builds a `Typed` certificate for a code entry from `Func_ok` in a module
context, using declared references. A body that uses no
data index may have a data space unrelated to the environment's.
-/

open Aeneas Aeneas.Std

namespace Itasca.CodeEntry

/-- Inversion of `Func_ok`: the locals are the declared locals, and the body is a typed expression
in the local context prepended to `C`. -/
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

/-- Generated function typing of a code entry in a module context gives a `Typed` certificate.
The context's element space must be the environment's, and its data space must be the
environment's unless the body uses no data index. -/
theorem Typed.of_func_ok {env : metadata.Env} {C : context} {idx : U32}
    {entry : Binary.Code} {ft : functype}
    (hc : ModuleContext env C)
    (he : C.ELEMS = Translation.Environment.elementTypes env)
    (hd : C.DATAS = Translation.Environment.dataTypes env ∨ Binary.instructionsUseData entry.body = false)
    (hf : Func_ok C (function idx entry) ft)
    (hdeclared : Spec.DeclaredReferences.Instructions
      (env.declared_funcs.val.map (fun idx => uN.mk_uN idx.val)) entry.body) : Typed env idx entry := by
  have hi : idx.val < env.types.val.length := by
    simpa [function, hc.types, proj_uN_0] using Module.Elaboration.func_index_bound hf
  have hft := Module.Elaboration.function_type_of_typing hf hc.types
  rw [Module.Elaboration.function_type_lookup hi] at hft
  obtain ⟨declared, params, results, hlocals, ht, hb⟩ := function_body hf
  have hd' : entry.declared.map Translation.valueType = declared := by
    have he := congrArg (List.map (fun l => match l with | _root_.local.LOCAL t => t)) hlocals
    simpa [List.map_map, Function.comp_def] using he
  subst declared
  rw [ht] at hft
  simp only [Translation.Environment.funcType, functype.mk_functype.injEq, list.mk_list.injEq] at hft
  obtain ⟨rfl, rfl⟩ := hft
  let ftype := env.types.val[idx.val]'hi
  have hcore : Body.Context.SameCore
      ((⟨[], [], [], [], [], [], [],
          ftype.params.val.map Translation.valueType ++ entry.declared.map Translation.valueType,
          [.mk_list (ftype.results.val.map Translation.valueType)],
          some (.mk_list (ftype.results.val.map Translation.valueType))⟩ : context) ++ C)
      (bodyContext env ftype.params.val entry.declared ftype.results.val) := by
    constructor
    · exact hc.types
    · exact hc.funcs
    · exact hc.globals
    · exact hc.tables
    · exact hc.mems
    · change (ftype.params.val.map Translation.valueType ++ entry.declared.map Translation.valueType) ++ C.LOCALS = _
      simp [bodyContext, hc.locals]
    · change [.mk_list (ftype.results.val.map Translation.valueType)] ++ C.LABELS = _
      simp [bodyContext, hc.labels]
    · rfl
  cases hb with
  | mk_Expr_ok ts hbody hw hws =>
    refine ⟨hi, ?_, hdeclared⟩
    rcases hd with hd | hno
    · apply Body.Context.instrs_transport_extend hbody _ _ hcore
      · change C.ELEMS.IsPrefix (Translation.Environment.elementTypes env)
        rw [he]
      · change C.DATAS.IsPrefix (Translation.Environment.dataTypes env)
        rw [hd]
    · exact Body.Context.instrs_transport_of_no_data hbody hno he hcore

end Itasca.CodeEntry

end
