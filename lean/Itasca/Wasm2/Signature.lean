import Itasca.Support.LiteralDispatch

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
theorem types.ValueType.eq_spec (a b : types.ValueType) :
    types.ValueType.Insts.CoreCmpPartialEqValueType.eq a b ⦃ equal =>
      equal = true ↔ a = b ⦄ := by
  cases a <;> cases b <;> simp [types.ValueType.Insts.CoreCmpPartialEqValueType.eq]

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

theorem signature.ResultType.len.complete (view : signature.ResultType) (env : module.Env)
    (ts : List types.ValueType) (hts : MultiValue.resolve env view = some ts) :
    ∃ n, signature.ResultType.len view env = .ok (.Ok n) ∧ n.val = ts.length := by
  obtain ⟨r, hr, hs⟩ := WP.spec_imp_exists (signature.ResultType.len.spec view env)
  cases r with
  | Err e => simp [hts] at hs
  | Ok n =>
    obtain ⟨us, hu, hn⟩ := hs
    have he : us = ts := by simpa [hts] using hu.symm
    exact ⟨n, hr, he ▸ hn⟩

theorem signature.ResultType.get.complete (view : signature.ResultType) (env : module.Env)
    (ts : List types.ValueType) (hts : MultiValue.resolve env view = some ts) (i : Usize) :
    signature.ResultType.get view env i = .ok (.Ok ts[i.val]?) := by
  obtain ⟨r, hr, hs⟩ := WP.spec_imp_exists (signature.ResultType.get.spec view env i)
  cases r with
  | Err e => simp [hts] at hs
  | Ok v =>
    obtain ⟨us, hu, hv⟩ := hs
    have he : us = ts := by simpa [hts] using hu.symm
    simpa [he, hv] using hr

end Itasca
