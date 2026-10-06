import Itasca.Generated.Funs
import «wasm2.0»

namespace Itasca.Translate

def valueType : types.ValueType → valtype
  | .I32 => .I32
  | .I64 => .I64
  | .F32 => .F32
  | .F64 => .F64

def mutability : types.Mut → «mut»
  | .Const => none
  | .Var => some .MUT

def globalType (g : types.GlobalType) : globaltype :=
  .mk_globaltype (mutability g.mutability) (valueType g.valtype)

theorem valueType_injective : Function.Injective valueType := by
  intro a b h
  cases a <;> cases b <;> simp_all [valueType]

theorem mutability_injective : Function.Injective mutability := by
  intro a b h
  cases a <;> cases b <;> simp_all [mutability]

/-- The extracted equality operation agrees with equality in the specification. -/
theorem valueType_eq (a b : types.ValueType) :
    types.ValueType.Insts.CoreCmpPartialEqValueType.eq a b =
      Aeneas.Std.Result.ok (decide (valueType a = valueType b)) := by
  cases a <;> cases b <;> rfl

/-- Covers every Rust global type, including immutable globals. -/
theorem globalType_valid (g : types.GlobalType) : Globaltype_ok (globalType g) :=
  .mk_Globaltype_ok _ _

end Itasca.Translate
