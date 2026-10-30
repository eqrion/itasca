import Itasca.Runtime.Representation.StoreInvariant

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- API reference values name an existing object of this store. The additional
encoding bounds rule out the reserved null sentinel wrapping around. -/
def ValueInStore {M : Type} (s : runtime.store.Store M) (value : runtime.Value) : Prop :=
  Interp.ValueOwnedFits s.id value ∧ match value with
  | .FuncRef (some a) => a.index.val < s.funcs.length
  | .ExternRef (some a) => a.index.val < s.externs.length
  | _ => True

/-- Encoding an owned typed API value establishes the canonical global-word
invariant, including reference ownership and scalar high-word zeros. -/
theorem encode_global_shape {M : Type} (s : runtime.store.Store M)
    (value : runtime.Value) (ty : Itasca.wasm_types.GlobalType)
    (ht : ty.valtype = Interp.rawType value) (hv : ValueInStore s value) :
    runtime.value.encode value ⦃ words => GlobalShape s {ty, lo := words.1, hi := words.2} ⦄ := by
  cases value <;> simp only [runtime.value.encode, GlobalShape, ht, Interp.rawType]
  all_goals simp [lift]
  case I32 v => scalar_tac
  case F32 v => scalar_tac
  case V128 v => step
  case FuncRef address =>
    cases address with
    | none => simp [ReferenceShape]
    | some a =>
      simp only [ValueInStore, Interp.ValueOwnedFits] at hv
      simp
      step as ⟨word, hword⟩
      right
      scalar_tac
  case ExternRef address =>
    cases address with
    | none => simp [ReferenceShape]
    | some a =>
      simp only [ValueInStore, Interp.ValueOwnedFits] at hv
      simp
      step as ⟨word, hword⟩
      right
      scalar_tac


def elementValueType : Itasca.wasm_types.ElemType → Itasca.wasm_types.ValueType
  | .FuncRef => .FuncRef
  | .ExternRef => .ExternRef

theorem encode_reference_shape {M : Type} (s : runtime.store.Store M)
    (value : runtime.Value) (ty : Itasca.wasm_types.ElemType)
    (ht : elementValueType ty = Interp.rawType value) (hv : ValueInStore s value) :
    runtime.value.encode value ⦃ words => ReferenceShape s ty words.1 ⦄ := by
  apply WP.spec_mono (encode_global_shape s value {valtype := elementValueType ty, mutability := .Const} ht hv)
  intro words hwords
  cases ty <;> exact hwords.1

end Itasca.Runtime.Store
