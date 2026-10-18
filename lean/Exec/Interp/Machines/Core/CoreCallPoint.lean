import Exec.Interp.Calls.CallReturnPoint
import Exec.Interp.Core.Point
namespace Exec.Interp
open Aeneas.Std
theorem coreEmission_not_call {C before after emitted index}
    (emission : Code.CoreEmission C before (.CALL (.mk_uN index)) emitted after) : False := by
  generalize equality : instr.CALL (.mk_uN index) = instruction at emission
  cases emission with
  | pure pure => rw [← equality] at pure; exact linearEmission_not_call pure
  | _ => simp [Abs.Memory.Load.source,Abs.Memory.Store.source] at equality

/-- A retained CALL certificate exposes its exact signature, argument base,
fetched instruction, and continuation; a preceding administrative jump remains
an explicit alternative. -/
theorem coreCodeRel_call_inv {C returns locals code labels stack pc next output after}
    (index : U32)
    (relation : Code.StructuredCode (Code.CoreEmission C) C.TYPES C.FUNCS returns locals code labels stack
      (.CALL (.mk_uN index.val) :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCode (Code.CoreEmission C) C.TYPES C.FUNCS returns locals code labels stack (.CALL (.mk_uN index.val) :: after) target.val next output) ∨
    (∃ front params results base,
      stack = front ++ params ∧ C.FUNCS[index.val]? = some ⟨.mk_list params, .mk_list results⟩ ∧
      base.val = Code.slots locals + Code.slots front ∧ code[pc]? = some (.Call index base) ∧
      Code.StructuredCode (Code.CoreEmission C) C.TYPES C.FUNCS returns locals code labels (front ++ results) after (pc + 1) next output) := by
  generalize hindex : index.val = sourceIndex at relation
  cases relation with
  | linear head fragment rest => exact False.elim (coreEmission_not_call head)
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | call signature arguments instruction rest =>
    rename_i actualIndex base
    have same : actualIndex = index := by scalar_tac
    subst actualIndex
    exact Or.inr ⟨_, _, _, _, rfl, signature, arguments, instruction, rest⟩

/-- Static CALL argument types identify the actual operand suffix and the
callee base. The continuation records the future returned values. -/
theorem coreCodeRel_call_values {C returns code labels pc next output after}
    (index : U32) (locals values : List val)
    (relation : Code.StructuredCode (Code.CoreEmission C) C.TYPES C.FUNCS returns (locals.map Code.valueType) code labels
      (values.map Code.valueType) (.CALL (.mk_uN index.val) :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCode (Code.CoreEmission C) C.TYPES C.FUNCS returns (locals.map Code.valueType) code labels
        (values.map Code.valueType) (.CALL (.mk_uN index.val) :: after) target.val next output) ∨
    (∃ front args params results base,
      values = front ++ args ∧ args.map Code.valueType = params ∧
      C.FUNCS[index.val]? = some ⟨.mk_list params, .mk_list results⟩ ∧
      base.val = Code.slots ((locals ++ front).map Code.valueType) ∧
      code[pc]? = some (.Call index base) ∧
      Code.StructuredCode (Code.CoreEmission C) C.TYPES C.FUNCS returns (locals.map Code.valueType) code labels
        (front.map Code.valueType ++ results) after (pc + 1) next output) := by
  rcases coreCodeRel_call_inv index relation with skip | actual
  · exact Or.inl skip
  · obtain ⟨frontTypes, params, results, base, stack, signature, arguments, instruction, rest⟩ := actual
    obtain ⟨front, args, split, frontTypesEq, argumentTypes⟩ := List.map_eq_append_iff.mp stack
    refine Or.inr ⟨front, args, params, results, base, split, argumentTypes, signature, ?_, instruction, ?_⟩
    · simpa only [List.map_append, Code.slots_append, frontTypesEq] using arguments
    · simpa only [frontTypesEq] using rest

end Exec.Interp
