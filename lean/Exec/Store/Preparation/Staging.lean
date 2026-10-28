import Exec.Store.Invariant.Rollback
import Exec.Store.Api.DefineTable
import Exec.Store.Invariant.InternTypes

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem StagedPrefix.refl {M : Type} (s : runtime.store.Store M) : StagedPrefix s s := by
  constructor <;> simp

private theorem prefix_trans {T : Type} (a b c : List T)
    (hab : b.take a.length = a) (hbc : c.take b.length = b) : c.take a.length = a := by
  have hlen : a.length ≤ b.length := by
    have h := congrArg List.length hab
    simp only [List.length_take] at h
    omega
  have h := congrArg (List.take a.length) hbc
  simpa [List.take_take, Nat.min_eq_left hlen, hab] using h

theorem StagedPrefix.trans {M : Type} {a b c : runtime.store.Store M}
    (hab : StagedPrefix a b) (hbc : StagedPrefix b c) : StagedPrefix a c where
  identity := hbc.identity.trans hab.identity
  limits := hbc.limits.trans hab.limits
  funcs := prefix_trans _ _ _ hab.funcs hbc.funcs
  types := prefix_trans _ _ _ hab.types hbc.types
  tables := prefix_trans _ _ _ hab.tables hbc.tables
  memories := prefix_trans _ _ _ hab.memories hbc.memories
  globals := prefix_trans _ _ _ hab.globals hbc.globals
  instances := prefix_trans _ _ _ hab.instances hbc.instances
  elems := prefix_trans _ _ _ hab.elems hbc.elems
  datas := prefix_trans _ _ _ hab.datas hbc.datas
  externs := hbc.externs.trans hab.externs
  instanceItems := hbc.instanceItems.trans hab.instanceItems

end Itasca.Runtime.Store
