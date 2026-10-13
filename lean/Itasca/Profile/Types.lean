import Itasca.Generated.Funs

/-!
# Profile signature predicates

Predicates on function types for `ValidationProfile.Wasm1` and `.Wasm2`: `FuncType` (language
restriction), `FuncTypeWithinLimits` (implementation bounds) and `FuncTypeAdmissible` (both),
lifted to the signature tables of a `module.Env` by `Environment` and `EnvironmentWithinLimits`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Profile

/-- The language restriction on a signature: Wasm 1.0 allows at most one result, Wasm 2.0 any
number. Allocation limits are separate. -/
def FuncType (profile : ValidationProfile) (ft : types.FuncType) : Prop :=
  match profile with
  | .Wasm1 => ft.results.val.length ≤ 1
  | .Wasm2 => True

/-- The implementation bounds on a signature, separate from language validity. Wasm 1.0 has none;
Wasm 2.0 bounds the parameter and result counts. -/
def FuncTypeWithinLimits (profile : ValidationProfile) (ft : types.FuncType) : Prop :=
  match profile with
  | .Wasm1 => True
  | .Wasm2 => ft.params.val.length ≤ limits.MAX_MULTI_VALUE_PARAMS.val ∧
      ft.results.val.length ≤ limits.MAX_MULTI_VALUE_RESULTS.val

/-- Every signature in the type table and the function signature cache satisfies `FuncType`. -/
def Environment (profile : ValidationProfile) (env : module.Env) : Prop :=
  (∀ ft ∈ env.types.val, FuncType profile ft) ∧
  (∀ ft ∈ env.func_types.val, FuncType profile ft)

/-- Every signature in the type table and the function signature cache satisfies
`FuncTypeWithinLimits`. -/
def EnvironmentWithinLimits (profile : ValidationProfile) (env : module.Env) : Prop :=
  (∀ ft ∈ env.types.val, FuncTypeWithinLimits profile ft) ∧
  (∀ ft ∈ env.func_types.val, FuncTypeWithinLimits profile ft)

/-- The condition the environment decoder checks: `FuncType` and `FuncTypeWithinLimits` together. -/
def FuncTypeAdmissible (profile : ValidationProfile) (ft : types.FuncType) : Prop :=
  match profile with
  | .Wasm1 => ft.results.val.length ≤ 1
  | .Wasm2 => ft.params.val.length ≤ limits.MAX_MULTI_VALUE_PARAMS.val ∧
      ft.results.val.length ≤ limits.MAX_MULTI_VALUE_RESULTS.val

/-- `FuncTypeAdmissible` is the conjunction of `FuncType` and `FuncTypeWithinLimits`. -/
theorem funcTypeAdmissible_iff (profile : ValidationProfile) (ft : types.FuncType) :
    FuncTypeAdmissible profile ft ↔ FuncType profile ft ∧ FuncTypeWithinLimits profile ft := by
  cases profile <;> simp [FuncTypeAdmissible, FuncType, FuncTypeWithinLimits]

end Itasca.Profile
