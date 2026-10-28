import Itasca.Runtime.Abs.Numeric.Decode
import Itasca.Runtime.Interp.Relations.LocalWrite
import Itasca.Runtime.Interp.Relations.Local

namespace Itasca.Runtime.Interp
open Aeneas.Std

theorem linearEmission_localGet_inv {locals before after : List valtype} {emitted : List Code.Bytecode}
    (index : Nat) (h : Code.LinearEmission locals before (.LOCAL_GET (.mk_uN index)) emitted after) :
    ∃ ty localSlot stackSlot,
      locals[index]? = some ty ∧
      emitted = [Code.move ty stackSlot localSlot] ∧ after = before ++ [ty] ∧
      localSlot.val = Code.offset locals index ∧
      stackSlot.val = Code.slots locals + Code.slots before := by
  generalize equality : instr.LOCAL_GET (.mk_uN index) = instruction at h
  cases h with
  | localGet stack ty idx localSlot stackSlot hty hlocal hstack =>
    simp only [instr.LOCAL_GET.injEq, uN.mk_uN.injEq] at equality
    subst index
    exact ⟨ty, localSlot, stackSlot, hty, rfl, rfl, hlocal, hstack⟩
  | binary stack ity op left right hl hr => cases op <;> simp_all [Code.IntegerBinary.source]
  | numeric stack op a b ha hb =>
    have decoded := congrArg Abs.Numeric.decodeInstruction equality
    rw [Abs.Numeric.decodeInstruction_source] at decoded
    simp [Abs.Numeric.decodeInstruction_source, Abs.Numeric.decodeInstruction] at decoded
  | _ => simp_all

theorem linearEmission_localWrite_inv {locals before after : List valtype} {emitted : List Code.Bytecode}
    (index : Nat) (keep : Bool)
    (h : Code.LinearEmission locals before
      (if keep then .LOCAL_TEE (.mk_uN index) else .LOCAL_SET (.mk_uN index)) emitted after) :
    ∃ stack ty localSlot stackSlot,
      before = stack ++ [ty] ∧ locals[index]? = some ty ∧
      emitted = [Code.move ty localSlot stackSlot] ∧ after = (if keep then stack ++ [ty] else stack) ∧
      localSlot.val = Code.offset locals index ∧
      stackSlot.val = Code.slots locals + Code.slots stack := by
  generalize equality : (if keep then instr.LOCAL_TEE (.mk_uN index) else .LOCAL_SET (.mk_uN index)) = instruction at h
  cases h with
  | localSet stack ty idx localSlot stackSlot hty hlocal hstack =>
    cases keep with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, instr.LOCAL_SET.injEq, uN.mk_uN.injEq] at equality
      subst index
      exact ⟨_, ty, localSlot, stackSlot, rfl, hty, rfl, rfl, hlocal, hstack⟩
    | true => simp at equality
  | localTee stack ty idx localSlot stackSlot hty hlocal hstack =>
    cases keep with
    | false => simp at equality
    | true =>
      simp only [↓reduceIte, instr.LOCAL_TEE.injEq, uN.mk_uN.injEq] at equality
      subst index
      exact ⟨_, ty, localSlot, stackSlot, rfl, hty, rfl, rfl, hlocal, hstack⟩
  | binary stack ity op left right hl hr => cases keep <;> cases op <;> simp_all [Code.IntegerBinary.source]
  | numeric stack op a b ha hb =>
    have decoded := congrArg Abs.Numeric.decodeInstruction equality
    rw [Abs.Numeric.decodeInstruction_source] at decoded
    cases keep <;> simp [Abs.Numeric.decodeInstruction_source, Abs.Numeric.decodeInstruction] at decoded
  | _ => cases keep <;> simp_all

end Itasca.Runtime.Interp
