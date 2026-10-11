import Itasca.Generated.Funs

open Aeneas Aeneas.Std

namespace Itasca.Profile

/-- Language restrictions on signatures, independently of allocation limits. -/
def FuncType (profile : ValidationProfile) (ft : types.FuncType) : Prop :=
  match profile with
  | .Wasm1 => ft.results.val.length ≤ 1
  | .Wasm2 => True

/-- Implementation signature bounds are separate from language validity.
The Wasm 1.0 profile preserves its existing parameter behavior. -/
def FuncTypeWithinLimits (profile : ValidationProfile) (ft : types.FuncType) : Prop :=
  match profile with
  | .Wasm1 => True
  | .Wasm2 => ft.params.val.length ≤ limits.MAX_MULTI_VALUE_PARAMS.val ∧
      ft.results.val.length ≤ limits.MAX_MULTI_VALUE_RESULTS.val

/-- Both direct and indexed calls use signatures admitted by the profile. -/
def Environment (profile : ValidationProfile) (env : module.Env) : Prop :=
  (∀ ft ∈ env.types.val, FuncType profile ft) ∧
  (∀ ft ∈ env.func_types.val, FuncType profile ft)

/-- Completeness bounds apply to the stored and cached signature tables. -/
def EnvironmentWithinLimits (profile : ValidationProfile) (env : module.Env) : Prop :=
  (∀ ft ∈ env.types.val, FuncTypeWithinLimits profile ft) ∧
  (∀ ft ∈ env.func_types.val, FuncTypeWithinLimits profile ft)

/-- The decoder checks both conditions; this form keeps the legacy result
bound definitionally unchanged in existing environment certificates. -/
def FuncTypeAdmissible (profile : ValidationProfile) (ft : types.FuncType) : Prop :=
  match profile with
  | .Wasm1 => ft.results.val.length ≤ 1
  | .Wasm2 => ft.params.val.length ≤ limits.MAX_MULTI_VALUE_PARAMS.val ∧
      ft.results.val.length ≤ limits.MAX_MULTI_VALUE_RESULTS.val

theorem funcTypeAdmissible_iff (profile : ValidationProfile) (ft : types.FuncType) :
    FuncTypeAdmissible profile ft ↔ FuncType profile ft ∧ FuncTypeWithinLimits profile ft := by
  cases profile <;> simp [FuncTypeAdmissible, FuncType, FuncTypeWithinLimits]

end Itasca.Profile
