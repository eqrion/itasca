import Exec.Abs.Numeric.Decode
import Exec.Interp.Numeric.Integer.EqzDispatch

namespace Exec.Interp
open Aeneas.Std

theorem linearEmission_eqz_inv {locals before after : List valtype} {emitted : List Code.Bytecode}
    (ty : Inn)
    (h : Code.LinearEmission locals before
      (.TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ)) emitted after) :
    ∃ stack slot,
      before = stack ++ [Code.integerType ty] ∧
      emitted = [eqzInstruction ty slot] ∧ after = stack ++ [.I32] ∧
      slot.val = Code.slots locals + Code.slots stack := by
  generalize equality : instr.TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ) = instruction at h
  cases h with
  | eqz32 stack slot position =>
    cases ty <;> simp_all [numtype_Inn]
    exact ⟨rfl, slot, by simp [eqzInstruction], position⟩
  | eqz64 stack slot position =>
    cases ty <;> simp_all [numtype_Inn]
    exact ⟨rfl, slot, by simp [eqzInstruction], position⟩
  | binary stack ity op left right hl hr => cases op <;> simp_all [Code.IntegerBinary.source]
  | numeric stack op a b ha hb =>
    have decoded := congrArg Abs.Numeric.decodeInstruction equality
    rw [Abs.Numeric.decodeInstruction_source] at decoded
    have selected : op = .eqz ty := by
      cases ty <;> simpa [Abs.Numeric.decodeInstruction, numtype_Inn] using decoded.symm
    subst op
    have same : b = a := by
      apply UScalar.eq_of_val_eq
      simpa [Abs.Numeric.Instruction.arity] using hb
    subst b
    refine ⟨stack, a, rfl, ?_, rfl, ha⟩
    cases ty <;> rfl
  | _ => simp_all

theorem linearCodeRel_eqz {locals before after : List valtype} {source : List instr}
    {code : List Code.Bytecode} {pc next : Nat} (ty : Inn)
    (relation : Code.LinearCodeRel locals before
      (.TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ) :: source) code pc next after) :
    ∃ stack slot,
      before = stack ++ [Code.integerType ty] ∧
      slot.val = Code.slots locals + Code.slots stack ∧
      code[pc]? = some (eqzInstruction ty slot) ∧
      Code.LinearCodeRel locals (stack ++ [.I32]) source code (pc + 1) next after := by
  obtain ⟨middle, emitted, head, fetch, tail⟩ := linearCodeRel_head relation
  obtain ⟨stack, slot, beforeEq, emittedEq, afterEq, position⟩ := linearEmission_eqz_inv ty head
  refine ⟨stack, slot, beforeEq, position, fetch _ [] emittedEq, ?_⟩
  simpa only [emittedEq, afterEq, List.length_singleton] using tail

theorem linearPoint_eqz {raw : runtime.interp.Frame} {f : Abs.AFrame}
    {compiled : runtime.bytecode.CompiledFunction} {next : Nat} {output : List valtype}
    (front : List val) (ty : Inn) (a : Nat) (after : List instr)
    (point : LinearPoint raw { f with
      code := .TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ) :: after,
      vals := front ++ [Abs.integerVal ty a] } compiled next output) :
    ∃ slot,
      slot.val = Code.slots ((f.locals ++ front).map Code.valueType) ∧
      compiled.code.val[raw.pc.val]? = some (eqzInstruction ty slot) ∧
      Code.LinearCodeRel (f.locals.map Code.valueType)
        ((front ++ [Abs.integerVal .I32 (if a = 0 then 1 else 0)]).map Code.valueType)
        after compiled.code.val (raw.pc.val + 1) next output := by
  have valueType (ty : Inn) (bits : Nat) : Code.valueType (Abs.integerVal ty bits) = Code.integerType ty := by
    cases ty <;> rfl
  obtain ⟨stack, slot, stackEq, position, fetch, tail⟩ := linearCodeRel_eqz ty point
  simp only [List.map_append, List.map_cons, List.map_nil, valueType] at stackEq
  have stackIs : front.map Code.valueType = stack := List.append_cancel_right stackEq
  subst stack
  refine ⟨slot, ?_, fetch, ?_⟩
  · simpa only [List.map_append, Code.slots_append] using position
  · simpa only [List.map_append, List.map_cons, List.map_nil, valueType, Code.integerType] using tail

end Exec.Interp
