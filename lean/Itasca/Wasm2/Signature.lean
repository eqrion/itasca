import Itasca.Support.LiteralDispatch

/-!
# Signature descriptors

`Wasm2.resolve` gives the list of value types denoted by a `signature.ResultType` descriptor in a
module environment. Specs of the extracted `signature.ResultType.len` and
`signature.ResultType.get` relate them to `resolve`, and the `complete` versions give acceptance
from independent premises.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- Logical list denoted by a descriptor; no such list is allocated by Rust. -/
def resolve (env : metadata.Env) : signature.ResultType → Option (List wasm_types.ValueType)
  | .Empty => some []
  | .One t => some [t]
  | .Type index part => (env.types.val[index.val]?).map fun ft =>
      match part with
      | .Params => ft.params.val
      | .Results => ft.results.val

end Itasca.Wasm2

namespace Itasca

@[step]
theorem wasm_types.ValueType.eq_spec (a b : wasm_types.ValueType) :
    wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq a b ⦃ equal =>
      equal = true ↔ a = b ⦄ := by
  cases a <;> cases b <;> simp [wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq]

@[step]
theorem signature.ResultType.len.spec (view : signature.ResultType) (env : metadata.Env) :
    signature.ResultType.len view env ⦃ r =>
      match r with
      | .Ok n => ∃ ts, Wasm2.resolve env view = some ts ∧ n.val = ts.length
      | .Err e => e = .UnknownType ∧ Wasm2.resolve env view = none ⦄ := by
  cases view with
  | Empty => simp [signature.ResultType.len, Wasm2.resolve]
  | One t => simp [signature.ResultType.len, Wasm2.resolve]
  | «Type» index part =>
    unfold signature.ResultType.len
    step*
    all_goals cases part <;> simp_all [Wasm2.resolve]
    all_goals have hi : index.val < env.types.val.length := by scalar_tac
    all_goals simp_all

@[step]
theorem signature.ResultType.get.spec (view : signature.ResultType) (env : metadata.Env) (i : Usize) :
    signature.ResultType.get view env i ⦃ r =>
      match r with
      | .Ok v => ∃ ts, Wasm2.resolve env view = some ts ∧ v = ts[i.val]?
      | .Err e => e = .UnknownType ∧ Wasm2.resolve env view = none ⦄ := by
  cases view with
  | Empty => simp [signature.ResultType.get, Wasm2.resolve]
  | One t =>
    unfold signature.ResultType.get
    step*
    all_goals simp_all [Wasm2.resolve] <;> omega
  | «Type» index part =>
    unfold signature.ResultType.get
    step*
    all_goals cases part <;> simp_all [Wasm2.resolve]
    all_goals have hi : index.val < env.types.val.length := by scalar_tac
    all_goals simp_all

theorem signature.ResultType.len.complete (view : signature.ResultType) (env : metadata.Env)
    (ts : List wasm_types.ValueType) (hts : Wasm2.resolve env view = some ts) :
    ∃ n, signature.ResultType.len view env = .ok (.Ok n) ∧ n.val = ts.length := by
  obtain ⟨r, hr, hs⟩ := WP.spec_imp_exists (signature.ResultType.len.spec view env)
  cases r with
  | Err e => simp [hts] at hs
  | Ok n =>
    obtain ⟨us, hu, hn⟩ := hs
    have he : us = ts := by simpa [hts] using hu.symm
    exact ⟨n, hr, he ▸ hn⟩

theorem signature.ResultType.get.complete (view : signature.ResultType) (env : metadata.Env)
    (ts : List wasm_types.ValueType) (hts : Wasm2.resolve env view = some ts) (i : Usize) :
    signature.ResultType.get view env i = .ok (.Ok ts[i.val]?) := by
  obtain ⟨r, hr, hs⟩ := WP.spec_imp_exists (signature.ResultType.get.spec view env i)
  cases r with
  | Err e => simp [hts] at hs
  | Ok v =>
    obtain ⟨us, hu, hv⟩ := hs
    have he : us = ts := by simpa [hts] using hu.symm
    simpa [he, hv] using hr

end Itasca
