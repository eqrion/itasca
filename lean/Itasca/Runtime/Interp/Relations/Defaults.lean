import Itasca.Runtime.Interp.Relations.Rel

namespace Itasca.Runtime.Interp

theorem encode_default_value {ty : valtype} {value : val}
    (default : SourceMachine.defaultValue ty = some value) :
    Compiler.encodeValue value = List.replicate (Compiler.width ty) 0 := by
  cases ty <;> simp only [SourceMachine.defaultValue, Option.some.injEq, reduceCtorEq] at default
  all_goals subst value
  all_goals simp [SourceMachine.integerVal, Compiler.encodeValue, Compiler.width,
    SpecExt.Builtins.floatBits, SpecExt.Builtins.magnitudeBits, List.replicate]


/-- The abstract defaults occupy exactly the zero words written by the real
callee initializer, including float +0, null references, and both vector slots. -/
theorem encode_default_locals (types : List valtype) (values : List val)
    (defaults : SourceMachine.defaultLocals (types.map local.LOCAL) = some values) :
    Compiler.encodeValues values = List.replicate (Compiler.slots types) 0 := by
  induction types generalizing values with
  | nil =>
    simp only [List.map_nil, SourceMachine.defaultLocals, Option.some.injEq] at defaults
    subst values
    rfl
  | cons ty types ih =>
    cases hv : SourceMachine.defaultValue ty with
    | none => simp [SourceMachine.defaultLocals, hv] at defaults
    | some value =>
      cases ht : SourceMachine.defaultLocals (types.map local.LOCAL) with
      | none => simp [SourceMachine.defaultLocals, hv, ht] at defaults
      | some tail =>
        simp [SourceMachine.defaultLocals, hv, ht] at defaults
        subst values
        change Compiler.encodeValue value ++ Compiler.encodeValues tail = List.replicate (Compiler.width ty + Compiler.slots types) 0
        rw [encode_default_value hv, ih tail ht, List.replicate_add]


theorem default_value_type {ty : valtype} {value : val}
    (default : SourceMachine.defaultValue ty = some value) : Compiler.valueType value = ty := by
  cases ty <;> simp only [SourceMachine.defaultValue, Option.some.injEq, reduceCtorEq] at default
  all_goals subst value
  all_goals rfl

/-- Default construction preserves the declared local type sequence exactly. -/
theorem default_locals_types (types : List valtype) (values : List val)
    (defaults : SourceMachine.defaultLocals (types.map local.LOCAL) = some values) :
    values.map Compiler.valueType = types := by
  induction types generalizing values with
  | nil =>
    simp only [List.map_nil, SourceMachine.defaultLocals, Option.some.injEq] at defaults
    subst values
    rfl
  | cons ty types ih =>
    cases hv : SourceMachine.defaultValue ty with
    | none => simp [SourceMachine.defaultLocals, hv] at defaults
    | some value =>
      cases ht : SourceMachine.defaultLocals (types.map local.LOCAL) with
      | none => simp [SourceMachine.defaultLocals, hv, ht] at defaults
      | some tail =>
        simp [SourceMachine.defaultLocals, hv, ht] at defaults
        subst values
        simp only [List.map_cons, default_value_type hv, ih tail ht]

end Itasca.Runtime.Interp

