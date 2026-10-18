import Exec.Abs.Numeric.Decode
import Exec.Interp.Relations.LocalWrite
import Exec.Interp.Relations.Local

namespace Exec.Interp
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

theorem linearPoint_localGet {raw : runtime.interp.Frame} {f : Abs.AFrame}
    {compiled : runtime.bytecode.CompiledFunction} {next : Nat} {output : List valtype}
    (index : Nat) (value : val) (after : List instr)
    (lookup : f.locals[index]? = some value)
    (point : LinearPoint raw { f with code := .LOCAL_GET (.mk_uN index) :: after } compiled next output) :
    ∃ src dst,
      src.val = Code.offset (f.locals.map Code.valueType) index ∧
      dst.val = Code.slots ((f.locals ++ f.vals).map Code.valueType) ∧
      compiled.code.val[raw.pc.val]? = some (Code.move (Code.valueType value) dst src) ∧
      Code.LinearCodeRel (f.locals.map Code.valueType)
        ((f.vals ++ [value]).map Code.valueType) after compiled.code.val (raw.pc.val + 1) next output := by
  obtain ⟨middle, emitted, head, fetch, tail⟩ := linearCodeRel_head point
  obtain ⟨ty, src, dst, localType, emittedEq, afterEq, source, destination⟩ := linearEmission_localGet_inv index head
  have typeLookup : (f.locals.map Code.valueType)[index]? = some (Code.valueType value) := by
    simpa using congrArg (Option.map Code.valueType) lookup
  have tyEq : ty = Code.valueType value := Option.some.inj (localType.symm.trans typeLookup)
  subst ty
  refine ⟨src, dst, source, ?_, fetch _ [] emittedEq, ?_⟩
  · simpa only [List.map_append, Code.slots_append] using destination
  · simpa only [emittedEq, afterEq, List.length_singleton, List.map_append, List.map_cons, List.map_nil, Bool.false_eq_true, ite_false, ite_true] using tail

theorem linearPoint_localWrite {raw : runtime.interp.Frame} {f : Abs.AFrame}
    {compiled : runtime.bytecode.CompiledFunction} {next : Nat} {output : List valtype}
    (index : Nat) (keep : Bool) (front : List val) (value old : val) (after : List instr)
    (lookup : f.locals[index]? = some old)
    (point : LinearPoint raw { f with
      code := (if keep then .LOCAL_TEE (.mk_uN index) else .LOCAL_SET (.mk_uN index)) :: after,
      vals := front ++ [value] } compiled next output) :
    ∃ src dst,
      Code.valueType value = Code.valueType old ∧
      src.val = Code.slots ((f.locals ++ front).map Code.valueType) ∧
      dst.val = Code.offset (f.locals.map Code.valueType) index ∧
      compiled.code.val[raw.pc.val]? = some (Code.move (Code.valueType value) dst src) ∧
      Code.LinearCodeRel ((f.locals.set index value).map Code.valueType)
        ((if keep then front ++ [value] else front).map Code.valueType)
        after compiled.code.val (raw.pc.val + 1) next output := by
  obtain ⟨middle, emitted, head, fetch, tail⟩ := linearCodeRel_head point
  obtain ⟨stack, ty, dst, src, stackEq, localType, emittedEq, afterEq, destination, source⟩ :=
    linearEmission_localWrite_inv index keep head
  simp only [List.map_append, List.map_cons, List.map_nil] at stackEq
  have split := List.append_inj' stackEq (by simp)
  have stackIs : front.map Code.valueType = stack := split.1
  have tyEq : Code.valueType value = ty := by simpa using split.2
  subst stack
  subst ty
  have typeLookup : (f.locals.map Code.valueType)[index]? = some (Code.valueType old) := by
    simpa using congrArg (Option.map Code.valueType) lookup
  have compatible : Code.valueType value = Code.valueType old := Option.some.inj (localType.symm.trans typeLookup)
  refine ⟨src, dst, compatible, ?_, destination, fetch _ [] emittedEq, ?_⟩
  · simpa only [List.map_append, Code.slots_append] using source
  · rw [Code.valueTypes_set lookup compatible]
    cases keep <;>
      simpa only [emittedEq, afterEq, List.length_singleton, List.map_append, List.map_cons, List.map_nil, Bool.false_eq_true, ite_false, ite_true] using tail

end Exec.Interp
