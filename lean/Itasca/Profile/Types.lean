import Itasca.Generated.Funs

/-!
# Profile signature predicates

Implementation bounds on function types and signature tables. The decoder-facing
`FuncTypeAdmissible` retains the current profile parameter.
-/

open Aeneas Aeneas.Std

namespace Itasca.Profile

/-- The implementation bounds on a signature, separate from language validity: the parameter and result counts are bounded. -/
def FuncTypeWithinLimits (ft : wasm_types.FuncType) : Prop :=
  ft.params.val.length ≤ limits.MAX_MULTI_VALUE_PARAMS.val ∧
    ft.results.val.length ≤ limits.MAX_MULTI_VALUE_RESULTS.val

theorem FuncTypeWithinLimits.bounds {ft : wasm_types.FuncType} (h : FuncTypeWithinLimits ft) :
    ft.params.val.length ≤ 1000 ∧ ft.results.val.length ≤ 1000 := by
  simpa [FuncTypeWithinLimits, limits.MAX_MULTI_VALUE_PARAMS, limits.MAX_MULTI_VALUE_RESULTS] using h

/-- Every signature in the type table and the function signature cache satisfies
`FuncTypeWithinLimits`. -/
structure EnvironmentWithinLimits (env : metadata.Env) : Prop where
  types : ∀ ft ∈ env.types.val, FuncTypeWithinLimits ft
  funcs : ∀ ft ∈ env.func_types.val, FuncTypeWithinLimits ft

/-- The signature bounds checked by the environment decoder. -/
def FuncTypeAdmissible (profile : ValidationProfile) (ft : wasm_types.FuncType) : Prop :=
  ft.params.val.length ≤ limits.MAX_MULTI_VALUE_PARAMS.val ∧
    ft.results.val.length ≤ limits.MAX_MULTI_VALUE_RESULTS.val

theorem funcTypeAdmissible_iff (profile : ValidationProfile) (ft : wasm_types.FuncType) :
    FuncTypeAdmissible profile ft ↔ FuncTypeWithinLimits ft := Iff.rfl

end Itasca.Profile
