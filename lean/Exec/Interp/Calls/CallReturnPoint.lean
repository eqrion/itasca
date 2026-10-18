import Exec.Abs.Numeric.Decode
import Exec.Interp.Control.StructuredPoint

namespace Exec.Interp
open Aeneas.Std

theorem linearEmission_not_call {locals before after emitted} {index : Nat}
    (h : Code.LinearEmission locals before (.CALL (.mk_uN index)) emitted after) : False := by
  generalize equality : instr.CALL (.mk_uN index) = instruction at h
  cases h with
  | binary stack ity op left right hl hr => cases op <;> simp_all [Code.IntegerBinary.source]
  | numeric stack op a b ha hb =>
    have decoded := congrArg Abs.Numeric.decodeInstruction equality
    rw [Abs.Numeric.decodeInstruction_source] at decoded
    simp [Abs.Numeric.decodeInstruction_source, Abs.Numeric.decodeInstruction] at decoded
  | _ => simp_all

theorem linearEmission_not_return {locals before after emitted}
    (h : Code.LinearEmission locals before .RETURN emitted after) : False := by
  generalize equality : instr.RETURN = instruction at h
  cases h with
  | binary stack ity op left right hl hr => cases op <;> simp_all [Code.IntegerBinary.source]
  | numeric stack op a b ha hb =>
    have decoded := congrArg Abs.Numeric.decodeInstruction equality
    rw [Abs.Numeric.decodeInstruction_source] at decoded
    simp [Abs.Numeric.decodeInstruction_source, Abs.Numeric.decodeInstruction] at decoded
  | _ => simp_all

/-- A retained CALL certificate exposes its exact signature, argument base,
fetched instruction, and continuation; a preceding administrative jump remains
an explicit alternative. -/
theorem codeRel_call_inv {types functions returns locals code labels stack pc next output after}
    (index : U32)
    (relation : Code.CodeRel types functions returns locals code labels stack
      (.CALL (.mk_uN index.val) :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.CodeRel types functions returns locals code labels stack (.CALL (.mk_uN index.val) :: after) target.val next output) ∨
    (∃ front params results base,
      stack = front ++ params ∧ functions[index.val]? = some ⟨.mk_list params, .mk_list results⟩ ∧
      base.val = Code.slots locals + Code.slots front ∧ code[pc]? = some (.Call index base) ∧
      Code.CodeRel types functions returns locals code labels (front ++ results) after (pc + 1) next output) := by
  generalize hindex : index.val = sourceIndex at relation
  cases relation with
  | linear head fragment rest => exact False.elim (linearEmission_not_call head)
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | call signature arguments instruction rest =>
    rename_i actualIndex base
    have same : actualIndex = index := by scalar_tac
    subst actualIndex
    exact Or.inr ⟨_, _, _, _, rfl, signature, arguments, instruction, rest⟩

/-- Explicit RETURN certificates provide the exact source and result-width
coordinates, without assuming any runtime behavior. -/
theorem codeRel_return_inv {types functions returns locals code labels stack pc next output after}
    (relation : Code.CodeRel types functions returns locals code labels stack (.RETURN :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.CodeRel types functions returns locals code labels stack (.RETURN :: after) target.val next output) ∨
    (∃ front src count,
      stack = front ++ returns ∧ src.val = Code.slots locals + Code.slots front ∧
      count.val = Code.slots returns ∧ code[pc]? = some (.Return src count)) := by
  cases relation with
  | linear head fragment rest => exact False.elim (linearEmission_not_return head)
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | return_ source size instruction remaining scope => exact Or.inr ⟨_, _, _, rfl, source, size, instruction⟩


/-- Static return stack types identify the actual result suffix and every
copied word coordinate. -/
theorem codeRel_return_values {types functions returns code labels pc next output after}
    (locals values : List val)
    (relation : Code.CodeRel types functions returns (locals.map Code.valueType) code labels
      (values.map Code.valueType) (.RETURN :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.CodeRel types functions returns (locals.map Code.valueType) code labels
        (values.map Code.valueType) (.RETURN :: after) target.val next output) ∨
    (∃ front results src count,
      values = front ++ results ∧ results.map Abs.valueType = returns ∧
      src.val = Code.slots ((locals ++ front).map Code.valueType) ∧
      count.val = Code.slots (results.map Code.valueType) ∧
      code[pc]? = some (.Return src count)) := by
  rcases codeRel_return_inv relation with skip | actual
  · exact Or.inl skip
  · obtain ⟨frontTypes, src, count, stack, source, size, instruction⟩ := actual
    obtain ⟨front, results, split, frontTypesEq, resultTypes⟩ := List.map_eq_append_iff.mp stack
    refine Or.inr ⟨front, results, src, count, split, ?_, ?_, ?_, instruction⟩
    · simpa only [show Code.valueType = Abs.valueType from funext valueType_eq_abs] using resultTypes
    · simpa only [List.map_append, Code.slots_append, frontTypesEq] using source
    · simpa only [resultTypes] using size

/-- Static CALL argument types identify the actual operand suffix and the
callee base. The continuation records the future returned values. -/
theorem codeRel_call_values {types functions returns code labels pc next output after}
    (index : U32) (locals values : List val)
    (relation : Code.CodeRel types functions returns (locals.map Code.valueType) code labels
      (values.map Code.valueType) (.CALL (.mk_uN index.val) :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.CodeRel types functions returns (locals.map Code.valueType) code labels
        (values.map Code.valueType) (.CALL (.mk_uN index.val) :: after) target.val next output) ∨
    (∃ front args params results base,
      values = front ++ args ∧ args.map Code.valueType = params ∧
      functions[index.val]? = some ⟨.mk_list params, .mk_list results⟩ ∧
      base.val = Code.slots ((locals ++ front).map Code.valueType) ∧
      code[pc]? = some (.Call index base) ∧
      Code.CodeRel types functions returns (locals.map Code.valueType) code labels
        (front.map Code.valueType ++ results) after (pc + 1) next output) := by
  rcases codeRel_call_inv index relation with skip | actual
  · exact Or.inl skip
  · obtain ⟨frontTypes, params, results, base, stack, signature, arguments, instruction, rest⟩ := actual
    obtain ⟨front, args, split, frontTypesEq, argumentTypes⟩ := List.map_eq_append_iff.mp stack
    refine Or.inr ⟨front, args, params, results, base, split, argumentTypes, signature, ?_, instruction, ?_⟩
    · simpa only [List.map_append, Code.slots_append, frontTypesEq] using arguments
    · simpa only [frontTypesEq] using rest

end Exec.Interp
