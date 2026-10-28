import Itasca.Runtime.Interp.Relations.Arguments
import Itasca.Support.Result
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem decode_value_owned_of_ok (ty : Itasca.types.ValueType) (lo hi : U64) (store : Usize)
    (value : runtime.Value) (actual : runtime.value.decode ty lo hi store = .ok value) : OwnedBy store value := by
  cases ty <;> simp only [runtime.value.decode,lift,bind_ok] at actual
  all_goals try { simp only [Result.ok.injEq] at actual; subst value; trivial }
  case V128 =>
    obtain ⟨shifted,shift,actual⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ actual
    simp only [lift,bind_ok,Result.ok.injEq] at actual
    subst value
    trivial
  all_goals
    split at actual
    · simp only [Result.ok.injEq] at actual; subst value; trivial
    · obtain ⟨index,subtracted,actual⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ actual
      simp only [Result.ok.injEq] at actual
      subst value
      rfl

theorem decode_slot_owned_of_ok (slots : Slice U64) (position : Usize)
    (ty : Itasca.types.ValueType) (store : Usize) (value : runtime.Value)
    (actual : runtime.interp.decode_slot slots position ty store = .ok value) : OwnedBy store value := by
  simp only [runtime.interp.decode_slot] at actual
  obtain ⟨width,widthEq,actual⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ actual
  obtain ⟨hi,hiEq,actual⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ actual
  obtain ⟨lo,loEq,actual⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ actual
  exact decode_value_owned_of_ok ty lo hi store value actual

end Itasca.Runtime.Interp
