import Itasca.Module.Const.Syntax
import Itasca.Spec.DeclaredReferences

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
