import Exec.Code.Local.Relations.Common.StatefulEmission
namespace Exec.Code

theorem linear_emission_not_indirect {locals before emitted after table type}
    (head : LinearEmission locals before (.CALL_INDIRECT table type) emitted after) : False := by
  generalize equal : instr.CALL_INDIRECT table type = instruction at head
  cases head with
  | binary stack ty op a b left right => cases op <;> cases equal
  | numeric stack op a b left right => cases op <;> cases equal
  | _ => cases equal

theorem core_emission_not_indirect {C before emitted after table type}
    (head : CoreEmission C before (.CALL_INDIRECT table type) emitted after) : False := by
  generalize equal : instr.CALL_INDIRECT table type = instruction at head
  cases head with
  | pure h => rw [← equal] at h; exact linear_emission_not_indirect h
  | load stack op argument address offset memory available sourceOffset slot => cases op <;> cases equal
  | store stack op argument address value offset memory available sourceOffset addressSlot valueSlot => cases op <;> cases equal
  | _ => cases equal

theorem float_emission_not_indirect {C before emitted after table type}
    (head : FloatCoreEmission C before (.CALL_INDIRECT table type) emitted after) : False := by
  generalize equal : instr.CALL_INDIRECT table type = instruction at head
  cases head with
  | core h => rw [← equal] at h; exact core_emission_not_indirect h
  | scalar stack op left right leftSlot rightSlot => cases op <;> cases equal

theorem stateful_emission_not_indirect {pairs C before emitted after table type}
    (head : StatefulEmission pairs C before (.CALL_INDIRECT table type) emitted after) : False := by
  generalize equal : instr.CALL_INDIRECT table type = instruction at head
  cases head with
  | instruction stack input output op signature first second a b entry firstSlot secondSlot arguments pair =>
    cases op <;> cases equal
end Exec.Code
