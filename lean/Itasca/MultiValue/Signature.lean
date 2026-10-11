import Itasca.Body.ScalarMatch

open Aeneas Aeneas.Std

namespace Itasca.MultiValue

/-- Logical list denoted by a descriptor; no such list is allocated by Rust. -/
def resolve (env : module.Env) : signature.ResultType → Option (List types.ValueType)
  | .Empty => some []
  | .One t => some [t]
  | .Type index part => (env.types.val[index.val]?).map fun ft =>
      match part with
      | .Params => ft.params.val
      | .Results => ft.results.val

end Itasca.MultiValue

namespace Itasca

@[step]
theorem signature.ResultType.len.spec (view : signature.ResultType) (env : module.Env) :
    signature.ResultType.len view env ⦃ r =>
      match r with
      | .Ok n => ∃ ts, MultiValue.resolve env view = some ts ∧ n.val = ts.length
      | .Err e => e = .UnknownType ∧ MultiValue.resolve env view = none ⦄ := by
  cases view with
  | Empty => simp [signature.ResultType.len, MultiValue.resolve]
  | One t => simp [signature.ResultType.len, MultiValue.resolve]
  | «Type» index part =>
    unfold signature.ResultType.len
    step*
    all_goals cases part <;> simp_all [MultiValue.resolve]
    all_goals have hi : index.val < env.types.val.length := by scalar_tac
    all_goals simp_all

@[step]
theorem signature.ResultType.get.spec (view : signature.ResultType) (env : module.Env) (i : Usize) :
    signature.ResultType.get view env i ⦃ r =>
      match r with
      | .Ok v => ∃ ts, MultiValue.resolve env view = some ts ∧ v = ts[i.val]?
      | .Err e => e = .UnknownType ∧ MultiValue.resolve env view = none ⦄ := by
  cases view with
  | Empty => simp [signature.ResultType.get, MultiValue.resolve]
  | One t =>
    unfold signature.ResultType.get
    step*
    all_goals simp_all [MultiValue.resolve] <;> omega
  | «Type» index part =>
    unfold signature.ResultType.get
    step*
    all_goals cases part <;> simp_all [MultiValue.resolve]
    all_goals have hi : index.val < env.types.val.length := by scalar_tac
    all_goals simp_all

end Itasca
