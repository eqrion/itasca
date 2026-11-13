import Itasca.Module.Const.Parser
import Itasca.Spec.Checks
import Itasca.Module.Readers.Utf8
import Itasca.Module.Elab.Translation
import Mathlib.Data.List.Forall2

/-!
Sections, each formerly its own module: References, Externals.
-/

/-! ## References -/

section

/-!
# Declared function references

The environment's `declared_funcs` cache lists the function indices mentioned by `ref.func`
initializers, function exports and element segments. `Coherent` ties the cache to `collected`, the
list computed from the environment's globals, exports and elements.
`metadata.declare_initializer.spec` and `metadata.Env.declares_function.spec` specify the cache update
and lookup.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleReferences

/-- The function indices declared by one constant expression. -/
def initializer : wasm_types.ConstExpr → List U32
  | .RefFunc index => [index]
  | _ => []

/-- The function indices declared by a global's initializer. -/
def global (entry : metadata.Global) : List U32 := initializer entry.init

/-- The function index declared by an export, if it exports a function. -/
def exportIndices (entry : metadata.Export) : List U32 :=
  match entry.desc with
  | .Func index => [index]
  | _ => []

/-- The function indices declared by an element segment's initializers. -/
def element (entry : metadata.Element) : List U32 := entry.init.val.flatMap initializer

/-- The declared function indices in parsing order: globals, then exports, then elements. Only
membership is observable, and repeated declarations appear as duplicates. -/
def collected (env : metadata.Env) : List U32 :=
  env.globals.val.flatMap global ++ env.exports.val.flatMap exportIndices ++
    env.elements.val.flatMap element

/-- The environment's `declared_funcs` cache equals `collected`. -/
def Coherent (env : metadata.Env) : Prop := env.declared_funcs.val = collected env

/-- `after` differs from `before` only by `declared_funcs` growing by `references`. -/
def Added (before after : metadata.Env) (references : List U32) : Prop :=
  after = { before with declared_funcs := after.declared_funcs } ∧
  after.declared_funcs.val = before.declared_funcs.val ++ references

/-- The declared indices of a constant expression match those the SpecTec reference collector finds
in its instruction form. -/
theorem initializer_indices (value : wasm_types.ConstExpr) :
    DeclaredReferences.instructionsIndices true (ModuleConstants.expression value) =
      (initializer value).map (fun index => uN.mk_uN index.val) := by
  cases value <;> simp [ModuleConstants.expression, ModuleConstants.instruction,
    initializer, DeclaredReferences.instructionsIndices, DeclaredReferences.instructionIndices,
    Spec.i32Const, ScalarConst.i64, ScalarConst.f32, ScalarConst.f64]

end Itasca.ModuleReferences

namespace Itasca

/-- `metadata.declare_initializer` appends the initializer's function indices to `declared_funcs`. -/
@[step]
theorem metadata.declare_initializer.spec (env : metadata.Env) (init : wasm_types.ConstExpr)
    (hbound : env.declared_funcs.val.length < Usize.max) :
    metadata.declare_initializer env init ⦃ result =>
      ModuleReferences.Added env result (ModuleReferences.initializer init) ⦄ := by
  cases init <;> simp only [metadata.declare_initializer, ModuleReferences.initializer]
  all_goals try (simp [ModuleReferences.Added])
  step
  simp [*]

/-- `metadata.Env.declares_function` terminates and computes membership in `declared_funcs`. -/
@[step]
theorem metadata.Env.declares_function.spec (env : metadata.Env) (index : U32) :
    metadata.Env.declares_function env index ⦃ result =>
      result = true ↔ index ∈ env.declared_funcs.val ⦄ := by
  unfold metadata.Env.declares_function metadata.Env.declares_function_loop
  apply loop.spec_decr_nat (fun pos => env.declared_funcs.val.length - pos.val)
    (fun pos => pos.val ≤ env.declared_funcs.val.length ∧
      ∀ j (hj : j < env.declared_funcs.val.length), j < pos.val →
        env.declared_funcs.val[j] ≠ index)
  · intro pos hp
    obtain ⟨hpos, hprefix⟩ := hp
    unfold metadata.Env.declares_function_loop.body
    step*
    · simp only [Bool.false_eq_true, false_iff]
      intro hm
      obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hm
      exact hprefix j hj (by scalar_tac) heq
    · simp only [true_iff]
      have hlt : pos.val < env.declared_funcs.val.length := by scalar_tac
      have heq : env.declared_funcs.val[pos.val] = index := by simpa [i2_post] using ‹i2 = index›
      rw [← heq]
      exact List.getElem_mem _
    · refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      intro j hj hlt
      by_cases hbefore : j < pos.val
      · exact hprefix j hj hbefore
      · have heq : j = pos.val := by scalar_tac
        simpa [i2_post, heq] using ‹¬i2 = index›
  · exact ⟨by simp, by simp⟩

/-- `metadata.Env.declares_function` returns exactly whether the index is in `declared_funcs`. -/
theorem metadata.Env.declares_function.eq (env : metadata.Env) (index : U32) :
    metadata.Env.declares_function env index = .ok (decide (index ∈ env.declared_funcs.val)) := by
  obtain ⟨result, hresult, hspec⟩ := WP.spec_imp_exists
    (metadata.Env.declares_function.spec env index)
  cases result <;> simp_all

end Itasca

end

/-! ## Externals -/

section

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

end
