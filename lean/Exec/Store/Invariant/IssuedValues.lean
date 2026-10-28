import Exec.Store.Invariant.ForeignValues
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- A public value is either owned by this store or carries a foreign store
identity. Same-store references must denote an issued address. -/
def IssuedValue {M : Type} (s : runtime.store.Store M) (value : runtime.Value) : Prop :=
  match value with
  | .FuncRef (some address) => address.store = s.id → address.index.val < s.funcs.length
  | .ExternRef (some address) => address.store = s.id → address.index.val < s.externs.length
  | _ => True

/-- Issued same-store values satisfy all actual slot-encoding bounds. -/
theorem issued_value_owned_or_foreign {M : Type} (s : runtime.store.Store M)
    (value : runtime.Value) (issued : IssuedValue s value) :
    ValueInStore s value ∨ ForeignValue s value := by
  cases value <;> simp only [IssuedValue, ValueInStore, ForeignValue, Interp.ValueOwnedFits] at issued ⊢
  all_goals try { exact Or.inl ⟨trivial, trivial⟩ }
  all_goals rename_i address
  all_goals cases address with
  | none => exact Or.inl ⟨trivial, trivial⟩
  | some address =>
    by_cases same : address.store = s.id
    · have bound := issued same
      left
      refine ⟨⟨same, ?_, ?_⟩, bound⟩
      · scalar_tac
      · rcases Usize.bounds_eq with h | h <;> scalar_tac
    · exact Or.inr same

end Itasca.Runtime.Store
