import Exec.Representation.Values

/-! Signature slot counting terminates on arbitrary type sequences. Overflow
is the sole error, with an exact mathematical size witness. -/
namespace Exec.Interp
open Aeneas Aeneas.Std

def typeSlots (types : List Itasca.types.ValueType) : Nat :=
  Code.slots (types.map sourceType)

def TypeSlotsState (total : Nat) (types : List Itasca.types.ValueType)
    (n i : Usize) : core.result.Result Unit runtime.ExecError → Prop
  | .Ok _ => n.val + typeSlots (types.drop i.val) = total
  | .Err error => error = .Exhausted .Values ∧ Usize.max < total

@[step] theorem type_slots_loop_effect (types : Slice Itasca.types.ValueType)
    (n i : Usize) (status : core.result.Result Unit runtime.ExecError)
    (total : Nat) (bound : i.val ≤ types.length)
    (state : TypeSlotsState total types.val n i status) :
    runtime.interp.type_slots_loop types n i status ⦃ (amount, result) =>
      match result with
      | .Ok _ => amount.val = total
      | .Err error => error = .Exhausted .Values ∧ Usize.max < total ⦄ := by
  unfold runtime.interp.type_slots_loop
  apply loop.spec_decr_nat (fun p => types.length - p.2.1.val)
    (fun p => p.2.1.val ≤ types.length ∧ TypeSlotsState total types.val p.1 p.2.1 p.2.2)
  · rintro ⟨amount, index, current⟩ ⟨hi, hs⟩
    dsimp only at hi hs
    unfold runtime.interp.type_slots_loop.body
    dsimp only
    split
    · have hb : index.val < types.val.length := by change index.val < types.length; scalar_tac
      cases current with
      | Err error => simpa [core.result.Result.is_ok, TypeSlotsState] using hs
      | Ok u =>
        cases u
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        simp only [TypeSlotsState] at hs
        rw [List.drop_eq_getElem_cons hb] at hs
        simp only [typeSlots, List.map_cons, Code.slots] at hs
        step as ⟨ty, hty⟩
        step with width_spec ty as ⟨width, hwidth⟩
        simp only [lift, bind_ok]
        have hc := Usize.checked_add_bv_spec amount (UScalar.cast .Usize width)
        cases he : Usize.checked_add amount (UScalar.cast .Usize width) with
        | none =>
          simp only [he] at hc ⊢
          step as ⟨next, hnext⟩
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          simp only [TypeSlotsState]
          constructor
          · trivial
          · rw [← hty] at hs
            have hw : (UScalar.cast .Usize width).val = Code.width (sourceType ty) := by
              simpa only [U32.cast_Usize_val_eq] using hwidth
            scalar_tac
        | some sum =>
          simp only [he] at hc ⊢
          step as ⟨next, hnext⟩
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          simp only [TypeSlotsState, typeSlots]
          rw [hnext]
          rw [← hty] at hs
          have hw : (UScalar.cast .Usize width).val = Code.width (sourceType ty) := by
            simpa only [U32.cast_Usize_val_eq] using hwidth
          scalar_tac
    · have hend : index.val = types.length := by scalar_tac
      have hdrop : types.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by change types.length ≤ index.val; omega)
      cases current <;> simpa [TypeSlotsState, hdrop, typeSlots, Code.slots] using hs
  · exact ⟨bound, state⟩

@[step] theorem type_slots_effect (types : Slice Itasca.types.ValueType) :
    runtime.interp.type_slots types ⦃ result =>
      match result with
      | .Ok amount => amount.val = typeSlots types.val
      | .Err error => error = .Exhausted .Values ∧ Usize.max < typeSlots types.val ⦄ := by
  unfold runtime.interp.type_slots
  step with type_slots_loop_effect types 0#usize 0#usize (.Ok ()) (typeSlots types.val)
    (by simp) (by simp [TypeSlotsState]) as ⟨amount, status, hs⟩
  cases status <;> simpa [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using hs

end Exec.Interp
