import Itasca.Module.Readers.Copies
import Itasca.Module.Elab.Translation
import Mathlib.Data.List.Forall2

/-!
# Import and export types

`ImportResolves` and `ExportResolves` give the declarative external type of an import or export
by looking up the environment's index spaces. `metadata.import_types.resolved` and
`metadata.export_types.resolved` show that the accessors `metadata.import_types` and
`metadata.export_types` return exactly a list of types that resolves entry by entry. `externalType`
translates an external type to SpecTec's `externtype`.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleExternals

/-- The external type `xt` is what import `imp` denotes, found by index-space lookup rather than by
running the accessor. -/
def ImportResolves (env : metadata.Env) (imp : metadata.Import) (xt : wasm_types.ExternType) : Prop :=
  match imp.desc with
  | .Func idx => ∃ hi : idx.val < env.types.val.length, xt = .Func env.types.val[idx.val]
  | .Table tt => xt = .Table tt
  | .Memory mt => xt = .Memory mt
  | .Global gt => xt = .Global gt

/-- The external type `xt` is what export `exp` denotes, looked up in the merged index spaces. -/
def ExportResolves (env : metadata.Env) (exp : metadata.Export) (xt : wasm_types.ExternType) : Prop :=
  match exp.desc with
  | .Func idx => ∃ hi : idx.val < env.func_types.val.length, xt = .Func env.func_types.val[idx.val]
  | .Table idx => ∃ hi : idx.val < env.table_types.val.length, xt = .Table env.table_types.val[idx.val]
  | .Memory idx => ∃ hi : idx.val < env.mem_types.val.length, xt = .Memory env.mem_types.val[idx.val]
  | .Global idx => ∃ hi : idx.val < env.global_types.val.length, xt = .Global env.global_types.val[idx.val]

/-- The SpecTec external type for an extracted external type. -/
def externalType : wasm_types.ExternType → externtype
  | .Func ft => .FUNC (EnvTranslation.funcType ft)
  | .Table tt => .TABLE (EnvTranslation.tableType tt)
  | .Memory mt => .MEM (EnvTranslation.memType mt)
  | .Global gt => .GLOBAL (Translate.globalType gt)

end Itasca.ModuleExternals

namespace Itasca

private theorem lookup_type_resolved (env : metadata.Env) (idx : U32)
    (hi : idx.val < env.types.val.length) :
    metadata.lookup_type env idx = .ok (.Ok env.types.val[idx.val]) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (metadata.lookup_type.spec env idx)
  cases r with
  | Ok ft =>
    obtain ⟨_, he⟩ := hp
    simpa [he] using hr
  | Err e =>
    have := hp.2
    omega

/-- The import loop of `metadata.import_types` returns the expected list when the imports resolve to
it. -/
theorem metadata.import_types_loop.resolved (env : metadata.Env) (expected : List wasm_types.ExternType)
    (hresolve : List.Forall₂ (ModuleExternals.ImportResolves env) env.imports.val expected)
    (out : alloc.vec.Vec wasm_types.ExternType) (i : Usize)
    (hi : i.val ≤ expected.length) (hout : out.val = expected.take i.val) :
    metadata.import_types_loop env out i ⦃ r =>
      ∃ result, r = .Ok result ∧ result.val = expected ⦄ := by
  have hlen := hresolve.length_eq
  have hbound : expected.length ≤ Usize.max := by rw [← hlen]; scalar_tac
  unfold metadata.import_types_loop
  apply loop.spec_decr_nat (fun p => expected.length - p.2.val)
    (fun p => p.2.val ≤ expected.length ∧ p.1.val = expected.take p.2.val)
  · rintro ⟨v, j⟩ ⟨hj, hv⟩
    dsimp only at hj hv
    unfold metadata.import_types_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : j.val = expected.length := by scalar_tac
      simp [heq] at hv
      exact ⟨v, rfl, hv⟩
    · rename_i hmore
      have hlt : j.val < env.imports.val.length := by scalar_tac
      have hlt' : j.val < expected.length := by omega
      have hcapacity : v.val.length < Usize.max := by
        simp only [hv, List.length_take, Nat.min_eq_left (by omega : j.val ≤ expected.length)]
        omega
      have he := hresolve.get hlt hlt'
      change ModuleExternals.ImportResolves env env.imports.val[j.val] expected[j.val] at he
      step
      rw [i2_post]
      cases hd : env.imports.val[j.val].desc with
      | Func idx =>
        simp only [ModuleExternals.ImportResolves, hd] at he
        obtain ⟨hidx, hxt⟩ := he
        dsimp only
        rw [lookup_type_resolved env idx hidx]
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step
        step
        refine ⟨?_, ?_, ?_⟩
        · scalar_tac
        · rw [out1_post, i3_post, hv, List.take_succ_eq_append_getElem hlt', hxt]
        · scalar_tac
      | Table tt =>
        simp only [ModuleExternals.ImportResolves, hd] at he
        step
        step
        refine ⟨?_, ?_, ?_⟩
        · scalar_tac
        · rw [r_post, i3_post, hv, List.take_succ_eq_append_getElem hlt', he]
        · scalar_tac
      | Memory mt =>
        simp only [ModuleExternals.ImportResolves, hd] at he
        step
        step
        refine ⟨?_, ?_, ?_⟩
        · scalar_tac
        · rw [r_post, i3_post, hv, List.take_succ_eq_append_getElem hlt', he]
        · scalar_tac
      | Global gt =>
        simp only [ModuleExternals.ImportResolves, hd] at he
        step
        step
        refine ⟨?_, ?_, ?_⟩
        · scalar_tac
        · rw [r_post, i3_post, hv, List.take_succ_eq_append_getElem hlt', he]
        · scalar_tac
  · exact ⟨hi, hout⟩

/-- `metadata.import_types` returns the independently resolved import types. -/
theorem metadata.import_types.resolved (env : metadata.Env) (expected : List wasm_types.ExternType)
    (hresolve : List.Forall₂ (ModuleExternals.ImportResolves env) env.imports.val expected) :
    metadata.import_types env ⦃ r => ∃ result, r = .Ok result ∧ result.val = expected ⦄ := by
  simpa [metadata.import_types] using metadata.import_types_loop.resolved env expected hresolve
    (alloc.vec.Vec.new _) 0#usize (by simp) (by simp)

/-- The export loop of `metadata.export_types` returns the expected list when the exports resolve
against the merged imported and defined index spaces. -/
theorem metadata.export_types_loop.resolved (env : metadata.Env) (expected : List wasm_types.ExternType)
    (hresolve : List.Forall₂ (ModuleExternals.ExportResolves env) env.exports.val expected)
    (out : alloc.vec.Vec wasm_types.ExternType) (i : Usize)
    (hi : i.val ≤ expected.length) (hout : out.val = expected.take i.val) :
    metadata.export_types_loop env out i ⦃ r =>
      ∃ result, r = .Ok result ∧ result.val = expected ⦄ := by
  have hlen := hresolve.length_eq
  have hbound : expected.length ≤ Usize.max := by rw [← hlen]; scalar_tac
  unfold metadata.export_types_loop
  apply loop.spec_decr_nat (fun p => expected.length - p.2.val)
    (fun p => p.2.val ≤ expected.length ∧ p.1.val = expected.take p.2.val)
  · rintro ⟨v, j⟩ ⟨hj, hv⟩
    dsimp only at hj hv
    unfold metadata.export_types_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : j.val = expected.length := by scalar_tac
      simp [heq] at hv
      exact ⟨v, rfl, hv⟩
    · rename_i hmore
      have hlt : j.val < env.exports.val.length := by scalar_tac
      have hlt' : j.val < expected.length := by omega
      have hcapacity : v.val.length < Usize.max := by
        simp only [hv, List.length_take, Nat.min_eq_left (by omega : j.val ≤ expected.length)]
        omega
      have he := hresolve.get hlt hlt'
      change ModuleExternals.ExportResolves env env.exports.val[j.val] expected[j.val] at he
      step
      rw [e_post]
      cases hd : env.exports.val[j.val].desc <;>
        simp only [ModuleExternals.ExportResolves, hd] at he <;>
        obtain ⟨hidx, hxt⟩ := he <;>
        step* <;>
        simp_all [List.take_succ_eq_append_getElem hlt'] <;> omega
  · exact ⟨hi, hout⟩

/-- `metadata.export_types` returns the independently resolved export types. -/
theorem metadata.export_types.resolved (env : metadata.Env) (expected : List wasm_types.ExternType)
    (hresolve : List.Forall₂ (ModuleExternals.ExportResolves env) env.exports.val expected) :
    metadata.export_types env ⦃ r => ∃ result, r = .Ok result ∧ result.val = expected ⦄ := by
  simpa [metadata.export_types] using metadata.export_types_loop.resolved env expected hresolve
    (alloc.vec.Vec.new _) 0#usize (by simp) (by simp)

end Itasca
