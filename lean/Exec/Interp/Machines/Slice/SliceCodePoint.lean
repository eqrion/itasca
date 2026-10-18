import Exec.Abs.Numeric.Decode
import Exec.Interp.Machines.Slice.SliceBinary

/-! Recover concrete instruction fetches and continuation certificates from
the compiler's exact emission relation. -/
namespace Exec.Interp
open Aeneas.Std

theorem linearEmission_slice_inv {locals before after : List valtype} {emitted : List Code.Bytecode}
    (ty : Inn) (operation : SliceBinary)
    (h : Code.LinearEmission locals before
      ((operation.operation.source ty)) emitted after) :
    ∃ stack left right,
      before = stack ++ [Code.integerType ty, Code.integerType ty] ∧
      emitted = [Code.IntegerBinary.target ty operation.operation left right] ∧
      after = stack ++ [Code.integerType (operation.resultType ty)] ∧
      left.val = Code.slots locals + Code.slots stack ∧ right.val = left.val + 1 := by
  generalize equality : (operation.operation.source ty) = instruction at h
  cases h with
  | binary stack ity op left right hl hr =>
    cases operation <;> cases ity <;> cases op <;> cases ty <;>
      simp_all [SliceBinary.operation, Code.IntegerBinary.source, numtype_Inn]
    all_goals exact ⟨left, right, rfl, rfl, hl, by omega⟩
  | numeric stack op a b ha hb =>
    have decoded := congrArg Abs.Numeric.decodeInstruction equality
    rw [Abs.Numeric.decodeInstruction_source] at decoded
    cases operation with
    | add =>
      have selected : op = .binary ty .ADD := by
        cases ty <;> simpa [SliceBinary.operation, Code.IntegerBinary.source, Abs.Numeric.decodeInstruction, numtype_Inn] using decoded.symm
      subst op
      refine ⟨stack, a, b, rfl, ?_, rfl, ha, hb⟩
      cases ty <;> rfl
    | sub =>
      have selected : op = .binary ty .SUB := by
        cases ty <;> simpa [SliceBinary.operation, Code.IntegerBinary.source, Abs.Numeric.decodeInstruction, numtype_Inn] using decoded.symm
      subst op
      refine ⟨stack, a, b, rfl, ?_, rfl, ha, hb⟩
      cases ty <;> rfl
    | eq =>
      have selected : op = .compare ty .EQ := by
        cases ty <;> simpa [SliceBinary.operation, Code.IntegerBinary.source, Abs.Numeric.decodeInstruction, numtype_Inn] using decoded.symm
      subst op
      refine ⟨stack, a, b, rfl, ?_, rfl, ha, hb⟩
      cases ty <;> rfl
    | ltU =>
      have selected : op = .compare ty (.LT .U) := by
        cases ty <;> simpa [SliceBinary.operation, Code.IntegerBinary.source, Abs.Numeric.decodeInstruction, numtype_Inn] using decoded.symm
      subst op
      refine ⟨stack, a, b, rfl, ?_, rfl, ha, hb⟩
      cases ty <;> rfl
  | _ => cases operation <;> simp_all [SliceBinary.operation, Code.IntegerBinary.source]

theorem linearCodeRel_slice {locals before after : List valtype} {source : List instr}
    {code : List Code.Bytecode} {pc next : Nat} (ty : Inn) (operation : SliceBinary)
    (relation : Code.LinearCodeRel locals before
      ((operation.operation.source ty) :: source) code pc next after) :
    ∃ stack left right,
      before = stack ++ [Code.integerType ty, Code.integerType ty] ∧
      left.val = Code.slots locals + Code.slots stack ∧ right.val = left.val + 1 ∧
      code[pc]? = some (Code.IntegerBinary.target ty operation.operation left right) ∧
      Code.LinearCodeRel locals (stack ++ [Code.integerType (operation.resultType ty)]) source code (pc + 1) next after := by
  obtain ⟨middle, emitted, head, fetch, tail⟩ := linearCodeRel_head relation
  obtain ⟨stack, left, right, beforeEq, emittedEq, afterEq, hl, hr⟩ := linearEmission_slice_inv ty operation head
  refine ⟨stack, left, right, beforeEq, hl, hr, fetch _ [] emittedEq, ?_⟩
  simpa only [emittedEq, afterEq, List.length_singleton] using tail

/-- Static stack positions are recovered from the live source values, rather
than supplied as an unrelated address assumption. -/
theorem linearPoint_slice {raw : runtime.interp.Frame} {f : Abs.AFrame}
    {compiled : runtime.bytecode.CompiledFunction} {next : Nat} {output : List valtype}
    (front : List val) (ty : Inn) (operation : SliceBinary) (a b : Nat) (after : List instr)
    (point : LinearPoint raw { f with
      code := (operation.operation.source ty) :: after,
      vals := front ++ [Abs.integerVal ty a, Abs.integerVal ty b] } compiled next output) :
    ∃ left right,
      left.val = Code.slots ((f.locals ++ front).map Code.valueType) ∧ right.val = left.val + 1 ∧
      compiled.code.val[raw.pc.val]? = some (Code.IntegerBinary.target ty operation.operation left right) ∧
      Code.LinearCodeRel (f.locals.map Code.valueType)
        ((front ++ [Abs.integerVal (operation.resultType ty) (operation.result ty a b)]).map Code.valueType)
        after compiled.code.val (raw.pc.val + 1) next output := by
  have valueType (ty : Inn) (bits : Nat) : Code.valueType (Abs.integerVal ty bits) = Code.integerType ty := by
    cases ty <;> rfl
  obtain ⟨stack, left, right, stackEq, hl, hr, fetch, tail⟩ := linearCodeRel_slice ty operation point
  simp only [List.map_append, List.map_cons, List.map_nil, valueType] at stackEq
  have stackIs : front.map Code.valueType = stack := List.append_cancel_right stackEq
  subst stack
  refine ⟨left, right, ?_, hr, fetch, ?_⟩
  · simpa only [List.map_append, Code.slots_append] using hl
  · simpa only [List.map_append, List.map_cons, List.map_nil, valueType] using tail

end Exec.Interp
