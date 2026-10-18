import Exec.Interp.StructuredMachine.OrdinaryHeads
import Exec.Interp.StructuredMachine.SuspendedPoint
import Exec.Interp.Calls.CallReturnPoint
namespace Exec.Interp.StructuredMachine
open Aeneas.Std
variable {jumpTables : List Aeneas.Std.U32}
variable {emission : ContextEmission} [OrdinaryHeads emission]
theorem codeRel_call_inv {C returns locals code labels stack pc next output after}
    (index : U32)
    (relation : Code.StructuredCodeWithTables (emission C) C.TYPES C.FUNCS returns locals code jumpTables labels stack
      (.CALL (.mk_uN index.val) :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCodeWithTables (emission C) C.TYPES C.FUNCS returns locals code jumpTables labels stack (.CALL (.mk_uN index.val) :: after) target.val next output) ∨
    (∃ front params results base,
      stack = front ++ params ∧ C.FUNCS[index.val]? = some ⟨.mk_list params, .mk_list results⟩ ∧
      base.val = Code.slots locals + Code.slots front ∧ code[pc]? = some (.Call index base) ∧
      Code.StructuredCodeWithTables (emission C) C.TYPES C.FUNCS returns locals code jumpTables labels (front ++ results) after (pc + 1) next output) := by
  generalize hindex : index.val = sourceIndex at relation
  cases relation with
  | linear head ordinary fragment rest => exact False.elim (emission_not_call head)
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | call signature arguments instruction rest =>
    rename_i actualIndex base
    have same : actualIndex = index := by scalar_tac
    subst actualIndex
    exact Or.inr ⟨_, _, _, _, rfl, signature, arguments, instruction, rest⟩

/-- Static CALL argument types identify the actual operand suffix and the
callee base. The continuation records the future returned values. -/
theorem codeRel_call_values {C returns code labels pc next output after}
    (index : U32) (locals values : List val)
    (relation : Code.StructuredCodeWithTables (emission C) C.TYPES C.FUNCS returns (locals.map Code.valueType) code jumpTables labels
      (values.map Code.valueType) (.CALL (.mk_uN index.val) :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCodeWithTables (emission C) C.TYPES C.FUNCS returns (locals.map Code.valueType) code jumpTables labels
        (values.map Code.valueType) (.CALL (.mk_uN index.val) :: after) target.val next output) ∨
    (∃ front args params results base,
      values = front ++ args ∧ args.map Code.valueType = params ∧
      C.FUNCS[index.val]? = some ⟨.mk_list params, .mk_list results⟩ ∧
      base.val = Code.slots ((locals ++ front).map Code.valueType) ∧
      code[pc]? = some (.Call index base) ∧
      Code.StructuredCodeWithTables (emission C) C.TYPES C.FUNCS returns (locals.map Code.valueType) code jumpTables labels
        (front.map Code.valueType ++ results) after (pc + 1) next output) := by
  rcases codeRel_call_inv index relation with skip | actual
  · exact Or.inl skip
  · obtain ⟨frontTypes, params, results, base, stack, signature, arguments, instruction, rest⟩ := actual
    obtain ⟨front, args, split, frontTypesEq, argumentTypes⟩ := List.map_eq_append_iff.mp stack
    refine Or.inr ⟨front, args, params, results, base, split, argumentTypes, signature, ?_, instruction, ?_⟩
    · simpa only [List.map_append, Code.slots_append, frontTypesEq] using arguments
    · simpa only [frontTypesEq] using rest

end Exec.Interp.StructuredMachine
