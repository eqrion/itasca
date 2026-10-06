import Itasca.Wasm1Profile
import Itasca.NumericMeaning
import Itasca.MemoryMeaning

open Aeneas Aeneas.Std

namespace Itasca

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem Numeric.opcode_profile (opcode : U8) (op : Numeric.Operation)
    (hmap : Numeric.opcodeMeaning opcode = some op) (C : context) :
    Wasm1.Instruction C op.instruction := by
  unfold Numeric.opcodeMeaning at hmap
  split at hmap <;> simp only [Option.some.injEq, reduceCtorEq] at hmap
  all_goals first | contradiction | subst op; exact .leaf _ _ trivial

set_option maxRecDepth 4096 in
theorem MemoryMeaning.opcode_profile (opcode : U8) (op : MemoryMeaning.Operation)
    (hmap : MemoryMeaning.opcodeMeaning opcode = some op) (C : context) (arg : code.MemArg) :
    Wasm1.Instruction C (op.op arg) := by
  unfold MemoryMeaning.opcodeMeaning at hmap
  split at hmap <;> simp only [Option.some.injEq, reduceCtorEq] at hmap
  all_goals first | contradiction | subst op; exact .leaf _ _ trivial

end Itasca
