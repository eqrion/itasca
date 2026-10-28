import Exec.Interp.Relations.Rel

namespace Itasca.Runtime.Interp

theorem encode_defaultValue {ty : valtype} {value : val}
    (default : Abs.defaultValue ty = some value) :
    Code.encodeValue value = List.replicate (Code.width ty) 0 := by
  cases ty <;> simp only [Abs.defaultValue, Option.some.injEq, reduceCtorEq] at default
  all_goals subst value
  all_goals simp [Abs.integerVal, Code.encodeValue, Code.width,
    SpecExt.Builtins.floatBits, SpecExt.Builtins.magnitudeBits, List.replicate]


/-- The abstract defaults occupy exactly the zero words written by the real
callee initializer, including float +0, null references, and both vector slots. -/
theorem encode_defaultLocals (types : List valtype) (values : List val)
    (defaults : Abs.defaultLocals (types.map local.LOCAL) = some values) :
    Code.encodeValues values = List.replicate (Code.slots types) 0 := by
  induction types generalizing values with
  | nil =>
    simp only [List.map_nil, Abs.defaultLocals, Option.some.injEq] at defaults
    subst values
    rfl
  | cons ty types ih =>
    cases hv : Abs.defaultValue ty with
    | none => simp [Abs.defaultLocals, hv] at defaults
    | some value =>
      cases ht : Abs.defaultLocals (types.map local.LOCAL) with
      | none => simp [Abs.defaultLocals, hv, ht] at defaults
      | some tail =>
        simp [Abs.defaultLocals, hv, ht] at defaults
        subst values
        change Code.encodeValue value ++ Code.encodeValues tail = List.replicate (Code.width ty + Code.slots types) 0
        rw [encode_defaultValue hv, ih tail ht, List.replicate_add]


theorem defaultValue_type {ty : valtype} {value : val}
    (default : Abs.defaultValue ty = some value) : Code.valueType value = ty := by
  cases ty <;> simp only [Abs.defaultValue, Option.some.injEq, reduceCtorEq] at default
  all_goals subst value
  all_goals rfl

/-- Default construction preserves the declared local type sequence exactly. -/
theorem defaultLocals_types (types : List valtype) (values : List val)
    (defaults : Abs.defaultLocals (types.map local.LOCAL) = some values) :
    values.map Code.valueType = types := by
  induction types generalizing values with
  | nil =>
    simp only [List.map_nil, Abs.defaultLocals, Option.some.injEq] at defaults
    subst values
    rfl
  | cons ty types ih =>
    cases hv : Abs.defaultValue ty with
    | none => simp [Abs.defaultLocals, hv] at defaults
    | some value =>
      cases ht : Abs.defaultLocals (types.map local.LOCAL) with
      | none => simp [Abs.defaultLocals, hv, ht] at defaults
      | some tail =>
        simp [Abs.defaultLocals, hv, ht] at defaults
        subst values
        simp only [List.map_cons, defaultValue_type hv, ih tail ht]

end Itasca.Runtime.Interp

