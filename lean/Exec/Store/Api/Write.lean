import Exec.Representation.StoreInvariant
import Exec.Store.Api.Grow
import Exec.Store.Invariant.ValueShape

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

@[simp] theorem value_type_exact (value : runtime.Value) :
    runtime.Value.value_type value = .ok (Interp.rawType value) := by
  cases value <;> rfl

theorem check_value_owned {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (s : runtime.store.Store M) (value : runtime.Value)
    (hv : Interp.ValueOwnedFits s.id value) :
    runtime.store.Store.check_value ops s value = .ok (.Ok ()) := by
  cases value <;> simp only [runtime.store.Store.check_value]
  case FuncRef address =>
    cases address with
    | none => rfl
    | some a => simp only [Interp.ValueOwnedFits] at hv; simp [runtime.store.Store.check, hv.1]
  case ExternRef address =>
    cases address with
    | none => rfl
    | some a => simp only [Interp.ValueOwnedFits] at hv; simp [runtime.store.Store.check, hv.1]

@[simp] theorem value_type_eq_self (ty : Itasca.types.ValueType) :
    types.ValueType.Insts.CoreCmpPartialEqValueType.eq ty ty = .ok true := by
  cases ty <;> rfl

@[simp] theorem element_value_type_exact (ty : Itasca.types.ElemType) :
    types.ElemType.value_type ty = .ok (elementValueType ty) := by
  cases ty <;> rfl

end Itasca.Runtime.Store
