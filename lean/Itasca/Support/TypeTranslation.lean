import Itasca.Generated.Funs
import «wasm2.0»

/-!
# Type translation

Translates the Rust value, reference, mutability and global types into their SpecTec counterparts
(`Translate.valueType`, `referenceType`, `mutability`, `globalType`), with injectivity and
equality-agreement lemmas.
-/

namespace Itasca.Translate

/-- The SpecTec value type of a Rust value type. -/
def valueType : wasm_types.ValueType → valtype
  | .I32 => .I32
  | .I64 => .I64
  | .F32 => .F32
  | .F64 => .F64
  | .V128 => .V128
  | .FuncRef => .FUNCREF
  | .ExternRef => .EXTERNREF

/-- The SpecTec reference type of a Rust element type. -/
def referenceType : wasm_types.ElemType → reftype
  | .FuncRef => .FUNCREF
  | .ExternRef => .EXTERNREF

/-- The SpecTec mutability of a Rust mutability. -/
def mutability : wasm_types.Mut → «mut»
  | .Const => none
  | .Var => some .MUT

/-- The SpecTec global type of a Rust global type. -/
def globalType (g : wasm_types.GlobalType) : globaltype :=
  .mk_globaltype (mutability g.mutability) (valueType g.valtype)

theorem valueType_injective : Function.Injective valueType := by
  intro a b h
  cases a <;> cases b <;> simp_all [valueType]

theorem mutability_injective : Function.Injective mutability := by
  intro a b h
  cases a <;> cases b <;> simp_all [mutability]

/-- The extracted equality operation agrees with equality in the specification. -/
theorem valueType_eq (a b : wasm_types.ValueType) :
    wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq a b =
      Aeneas.Std.Result.ok (decide (valueType a = valueType b)) := by
  cases a <;> cases b <;> rfl

/-- The translation of every Rust global type, mutable or not, satisfies `Globaltype_ok`. -/
theorem globalType_valid (g : wasm_types.GlobalType) : Globaltype_ok (globalType g) :=
  .mk_Globaltype_ok _ _

end Itasca.Translate
