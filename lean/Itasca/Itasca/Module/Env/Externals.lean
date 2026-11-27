import Itasca.Module.Definitions
import Itasca.Results.Definitions.Validation
import Itasca.Module.Const.Parser
import Itasca.Spec.Typing
import Itasca.Module.Readers.Syntax
import Itasca.Module.Elab.Translation
import Mathlib.Data.List.Forall2
import Itasca.Module.Elab.SegmentTyping

open WebAssembly

/-!
Proofs for Module / Env.

This module collects Externals, Basic.
Each section documents its contracts and consumers.
-/

/-! ## Externals -/

section

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

namespace Itasca.Module.References

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
    Spec.DeclaredReferences.instructionsIndices true (Module.Constants.expression value) =
      (initializer value).map (fun index => uN.mk_uN index.val) := by
  cases value <;> simp [Module.Constants.expression, Module.Constants.instruction,
    initializer, Spec.DeclaredReferences.instructionsIndices, Spec.DeclaredReferences.instructionIndices,
    Spec.i32Const, Spec.Constants.i64, Spec.Constants.f32, Spec.Constants.f64]

end Itasca.Module.References

namespace Itasca

/-- `metadata.declare_initializer` appends the initializer's function indices to `declared_funcs`. -/
@[step]
theorem metadata.declare_initializer.spec (env : metadata.Env) (init : wasm_types.ConstExpr)
    (hbound : env.declared_funcs.val.length < Usize.max) :
    metadata.declare_initializer env init ⦃ result =>
      Module.References.Added env result (Module.References.initializer init) ⦄ := by
  cases init <;> simp only [metadata.declare_initializer, Module.References.initializer]
  all_goals try (simp [Module.References.Added])
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
by looking up the environment's index spaces. `metadata.Env.import_types.resolved` and
`metadata.Env.export_types.resolved` show that the accessors `metadata.Env.import_types` and
`metadata.Env.export_types` return exactly a list of types that resolves entry by entry. `externalType`
translates an external type to SpecTec's `externtype`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Externals

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

end Itasca.Module.Externals

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

/-- The import loop of `metadata.Env.import_types` returns the expected list when the imports resolve to
it. -/
theorem metadata.Env.import_types_loop.resolved (env : metadata.Env) (expected : List wasm_types.ExternType)
    (hresolve : List.Forall₂ (Module.Externals.ImportResolves env) env.imports.val expected)
    (out : alloc.vec.Vec wasm_types.ExternType) (i : Usize)
    (hi : i.val ≤ expected.length) (hout : out.val = expected.take i.val) :
    metadata.Env.import_types_loop env out i ⦃ r =>
      ∃ result, r = .Ok result ∧ result.val = expected ⦄ := by
  have hlen := hresolve.length_eq
  have hbound : expected.length ≤ Usize.max := by rw [← hlen]; scalar_tac
  unfold metadata.Env.import_types_loop
  apply loop.spec_decr_nat (fun p => expected.length - p.2.val)
    (fun p => p.2.val ≤ expected.length ∧ p.1.val = expected.take p.2.val)
  · rintro ⟨v, j⟩ ⟨hj, hv⟩
    dsimp only at hj hv
    unfold metadata.Env.import_types_loop.body
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
      change Module.Externals.ImportResolves env env.imports.val[j.val] expected[j.val] at he
      step
      rw [i2_post]
      cases hd : env.imports.val[j.val].desc with
      | Func idx =>
        simp only [Module.Externals.ImportResolves, hd] at he
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
        simp only [Module.Externals.ImportResolves, hd] at he
        step
        step
        refine ⟨?_, ?_, ?_⟩
        · scalar_tac
        · rw [r_post, i3_post, hv, List.take_succ_eq_append_getElem hlt', he]
        · scalar_tac
      | Memory mt =>
        simp only [Module.Externals.ImportResolves, hd] at he
        step
        step
        refine ⟨?_, ?_, ?_⟩
        · scalar_tac
        · rw [r_post, i3_post, hv, List.take_succ_eq_append_getElem hlt', he]
        · scalar_tac
      | Global gt =>
        simp only [Module.Externals.ImportResolves, hd] at he
        step
        step
        refine ⟨?_, ?_, ?_⟩
        · scalar_tac
        · rw [r_post, i3_post, hv, List.take_succ_eq_append_getElem hlt', he]
        · scalar_tac
  · exact ⟨hi, hout⟩

/-- `metadata.Env.import_types` returns the independently resolved import types. -/
theorem metadata.Env.import_types.resolved (env : metadata.Env) (expected : List wasm_types.ExternType)
    (hresolve : List.Forall₂ (Module.Externals.ImportResolves env) env.imports.val expected) :
    metadata.Env.import_types env ⦃ r => ∃ result, r = .Ok result ∧ result.val = expected ⦄ := by
  simpa [metadata.Env.import_types] using metadata.Env.import_types_loop.resolved env expected hresolve
    (alloc.vec.Vec.new _) 0#usize (by simp) (by simp)

/-- The export loop of `metadata.Env.export_types` returns the expected list when the exports resolve
against the merged imported and defined index spaces. -/
theorem metadata.Env.export_types_loop.resolved (env : metadata.Env) (expected : List wasm_types.ExternType)
    (hresolve : List.Forall₂ (Module.Externals.ExportResolves env) env.exports.val expected)
    (out : alloc.vec.Vec wasm_types.ExternType) (i : Usize)
    (hi : i.val ≤ expected.length) (hout : out.val = expected.take i.val) :
    metadata.Env.export_types_loop env out i ⦃ r =>
      ∃ result, r = .Ok result ∧ result.val = expected ⦄ := by
  have hlen := hresolve.length_eq
  have hbound : expected.length ≤ Usize.max := by rw [← hlen]; scalar_tac
  unfold metadata.Env.export_types_loop
  apply loop.spec_decr_nat (fun p => expected.length - p.2.val)
    (fun p => p.2.val ≤ expected.length ∧ p.1.val = expected.take p.2.val)
  · rintro ⟨v, j⟩ ⟨hj, hv⟩
    dsimp only at hj hv
    unfold metadata.Env.export_types_loop.body
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
      change Module.Externals.ExportResolves env env.exports.val[j.val] expected[j.val] at he
      step
      rw [e_post]
      cases hd : env.exports.val[j.val].desc <;>
        simp only [Module.Externals.ExportResolves, hd] at he <;>
        obtain ⟨hidx, hxt⟩ := he <;>
        step* <;>
        simp_all [List.take_succ_eq_append_getElem hlt'] <;> omega
  · exact ⟨hi, hout⟩

/-- `metadata.Env.export_types` returns the independently resolved export types. -/
theorem metadata.Env.export_types.resolved (env : metadata.Env) (expected : List wasm_types.ExternType)
    (hresolve : List.Forall₂ (Module.Externals.ExportResolves env) env.exports.val expected) :
    metadata.Env.export_types env ⦃ r => ∃ result, r = .Ok result ∧ result.val = expected ⦄ := by
  simpa [metadata.Env.export_types] using metadata.Env.export_types_loop.resolved env expected hresolve
    (alloc.vec.Vec.new _) 0#usize (by simp) (by simp)

end Itasca

end

end

/-! ## Basic -/

section

/-!
# Decoded module environments

Invariants of the `metadata.Env` built by `metadata.validate_env`. `Cache` says the merged index
spaces are imports followed by definitions, `Valid` collects the semantic checks that can be
read off the environment, and `Bounded` tracks the cursor-relative size bounds used for
overflow-free arithmetic. `metadata.Env.new.spec` shows the empty environment satisfies all three.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Environment

/-- The semantic checks that are stored in, or derivable from, the environment in the module.
Byte-format evidence is tracked separately. -/
structure Valid (env : metadata.Env) : Prop where
  types : ∀ ft ∈ env.types.val, CodeEntry.FuncTypeWithinLimits ft
  tables : ∀ tt ∈ env.table_types.val, Module.Translation.LimitsValid tt.limits (2 ^ 32 - 1)
  memories : ∀ mt ∈ env.mem_types.val, Module.Translation.LimitsValid mt.limits (2 ^ 16)
  memoryCount : env.mem_types.val.length ≤ 1
  globals : ∀ g ∈ env.globals.val, Module.Constants.Valid env g.init g.gtype.valtype
  imports : ∀ entry ∈ env.imports.val,
    Binary.Utf8 entry.module.val ∧ Binary.Utf8 entry.name.val
  exportNames : ∀ entry ∈ env.exports.val, Binary.Utf8 entry.name.val
  distinctExports : (env.exports.val.map fun entry => entry.name.val).Nodup
  exports : ∀ entry ∈ env.exports.val, ∃ xt, Module.Externals.ExportResolves env entry xt
  start : ∀ idx, env.start = some idx → ∃ hi : idx.val < env.func_types.val.length,
    env.func_types.val[idx.val].params.val = [] ∧ env.func_types.val[idx.val].results.val = []
  elements : ∀ entry ∈ env.elements.val, Module.Segments.elementValid env entry
  references : Module.References.Coherent env

/-- Every list length and counter in the environment is at most the byte cursor `pos`, which
keeps allocation and counter arithmetic within range. -/
structure Bounded (env : metadata.Env) (pos : Nat) : Prop where
  types : env.types.val.length ≤ pos
  imports : env.imports.val.length ≤ pos
  globals : env.globals.val.length ≤ pos
  exports : env.exports.val.length ≤ pos
  elements : env.elements.val.length ≤ pos
  funcIndices : env.func_type_indices.val.length ≤ pos
  funcs : env.func_types.val.length ≤ pos
  tables : env.table_types.val.length ≤ pos
  memories : env.mem_types.val.length ≤ pos
  globalTypes : env.global_types.val.length ≤ pos
  numFuncs : env.num_imported_funcs.val ≤ pos
  numGlobals : env.num_imported_globals.val ≤ pos
  declaredFuncs : env.declared_funcs.val.length ≤ pos

theorem Bounded.mono {env pos next} (h : Bounded env pos) (hle : pos ≤ next) :
    Bounded env next := by
  cases h
  constructor <;> omega

theorem Cache.global_prefix {env tables memories} (h : Cache env tables memories) :
    env.global_types.val.take env.num_imported_globals.val = importedGlobals env.imports.val := by
  rw [h.globals, h.numGlobals, List.take_left]

theorem Cache.func_property {env tables memories} (h : Cache env tables memories)
    {P : wasm_types.FuncType → Prop} (ht : ∀ ft ∈ env.types.val, P ft) :
    ∀ ft ∈ env.func_types.val, P ft := by
  intro ft hf
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hf
  have hj' : j < (importedFuncs env.imports.val ++ env.func_type_indices.val).length := by rw [h.funcs.length_eq]; exact hj
  obtain ⟨hi, he⟩ := h.funcs.get hj' hj
  simp only [List.get_eq_getElem] at he
  rw [← he]
  exact ht _ (List.getElem_mem hi)

/-- In a valid cached environment, the stored and cached signatures also respect the completeness
limits. -/
theorem Valid.environment_within_limits {env tables memories} (hv : Valid env)
    (hc : Cache env tables memories) : CodeEntry.EnvironmentWithinLimits env := by
  have ht : ∀ ft ∈ env.types.val, CodeEntry.FuncTypeWithinLimits ft := by
    intro ft hm
    exact hv.types ft hm
  exact ⟨ht, hc.func_property ht⟩

theorem Cache.import_indices {env tables memories} (h : Cache env tables memories) :
    ∀ idx ∈ importedFuncs env.imports.val, idx.val < env.types.val.length := by
  intro idx hi
  have hm : idx ∈ importedFuncs env.imports.val ++ env.func_type_indices.val := List.mem_append_left _ hi
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hm
  have hj' : j < env.func_types.val.length := by rw [← h.funcs.length_eq]; exact hj
  have hr := h.funcs.get hj hj'
  simp only [List.get_eq_getElem] at hr
  rw [he] at hr
  exact hr.1

/-- Every import of a cached environment has a resolved external type. -/
theorem Cache.imports_resolve {env tables memories} (h : Cache env tables memories) :
    ∃ xts, List.Forall₂ (Module.Externals.ImportResolves env) env.imports.val xts := by
  have hb := h.import_indices
  generalize env.imports.val = entries at hb ⊢
  induction entries with
  | nil => exact ⟨[], .nil⟩
  | cons entry entries ih =>
    have hb' : ∀ idx ∈ importedFuncs entries, idx.val < env.types.val.length := by
      intro idx hi
      apply hb idx
      cases entry.desc <;> simp_all [importedFuncs]
    obtain ⟨rest, hr⟩ := ih hb'
    cases hd : entry.desc with
    | Func idx =>
      have hi : idx.val < env.types.val.length := hb idx (by simp [importedFuncs, hd])
      exact ⟨.Func env.types.val[idx.val] :: rest, .cons (by simpa [Module.Externals.ImportResolves, hd] using (show ∃ hj : idx.val < env.types.val.length, (wasm_types.ExternType.Func env.types.val[idx.val]) = .Func env.types.val[idx.val] from ⟨hi, rfl⟩)) hr⟩
    | Table tt => exact ⟨.Table tt :: rest, .cons (by simp [Module.Externals.ImportResolves, hd]) hr⟩
    | Memory mt => exact ⟨.Memory mt :: rest, .cons (by simp [Module.Externals.ImportResolves, hd]) hr⟩
    | Global gt => exact ⟨.Global gt :: rest, .cons (by simp [Module.Externals.ImportResolves, hd]) hr⟩

theorem Valid.exports_resolve {env} (h : Valid env) :
    ∃ xts, List.Forall₂ (Module.Externals.ExportResolves env) env.exports.val xts := by
  have he := h.exports
  generalize env.exports.val = entries at he ⊢
  induction entries with
  | nil => exact ⟨[], .nil⟩
  | cons entry entries ih =>
    obtain ⟨xt, ht⟩ := he entry (by simp)
    obtain ⟨xts, hrest⟩ := ih (by intro entry hm; exact he entry (by simp [hm]))
    exact ⟨xt :: xts, .cons ht hrest⟩

end Itasca.Module.Environment

namespace Itasca

/-- The empty environment is cached, valid and bounded by `0`. -/
@[step]
theorem metadata.Env.new.spec : metadata.Env.new ⦃ env =>
    Module.Environment.Cache env [] [] ∧ Module.Environment.Valid env ∧ Module.Environment.Bounded env 0 ⦄ := by
  unfold metadata.Env.new
  simp only [WP.spec_ok]
  constructor
  · constructor <;> simp [Module.Environment.importedFuncs, Module.Environment.importedGlobals,
      Module.Environment.importedTables, Module.Environment.importedMems]
  · constructor
    · constructor <;> simp [Module.References.Coherent, Module.References.collected]
    · constructor <;> simp

end Itasca

end
