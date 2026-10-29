import Itasca.Runtime.Compiler.Local.Relations.Instructions.SlotCheckAcceptance

/-!
Scalar operator checking accepts the exact projection supplied by lowering when its three concrete word slots fit the function's retained capacity.

Main declarations: `scalar_instruction_accepts` and `store_instruction_accepts`. A direct consumer is `Compiler.Local.Relations.Instructions.SimdInstructionAcceptance`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Scalar operator checking accepts the exact projection supplied by lowering
when its three concrete word slots fit the function's retained capacity. -/
theorem scalar_instruction_accepts (function : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) (opcode : U16) (dst left right : U32)
    (projected : runtime.bytecode.Instr.scalar instruction = .ok (some (opcode,dst,left,right)))
    (destination : dst.val+1 ≤ function.slot_count.val)
    (first : left.val+1 ≤ function.slot_count.val) (second : right.val+1 ≤ function.slot_count.val) :
    runtime.bytecode.CompiledFunction.instruction_valid function instruction = .ok true := by
  simp [runtime.bytecode.CompiledFunction.instruction_valid,projected,
    slots_fit_accepts function dst 1#u32 destination,slots_fit_accepts function left 1#u32 first,
    slots_fit_accepts function right 1#u32 second]

/-- Load checking accepts from the projected destination and address bounds. -/
theorem load_instruction_accepts (function : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) (opcode : U16) (dst address offset : U32)
    (scalar : runtime.bytecode.Instr.scalar instruction = .ok none)
    (projected : runtime.bytecode.Instr.load instruction = .ok (some (opcode,dst,address,offset)))
    (destination : dst.val+1 ≤ function.slot_count.val) (input : address.val+1 ≤ function.slot_count.val) :
    runtime.bytecode.CompiledFunction.instruction_valid function instruction = .ok true := by
  simp [runtime.bytecode.CompiledFunction.instruction_valid,scalar,projected,
    slots_fit_accepts function dst 1#u32 destination,slots_fit_accepts function address 1#u32 input]

/-- Store checking accepts from the projected address and value bounds. -/
theorem store_instruction_accepts (function : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) (opcode : U16) (address value offset : U32)
    (scalar : runtime.bytecode.Instr.scalar instruction = .ok none)
    (load : runtime.bytecode.Instr.load instruction = .ok none)
    (projected : runtime.bytecode.Instr.store instruction = .ok (some (opcode,address,value,offset)))
    (input : address.val+1 ≤ function.slot_count.val) (stored : value.val+1 ≤ function.slot_count.val) :
    runtime.bytecode.CompiledFunction.instruction_valid function instruction = .ok true := by
  simp [runtime.bytecode.CompiledFunction.instruction_valid,scalar,load,projected,
    slots_fit_accepts function address 1#u32 input,slots_fit_accepts function value 1#u32 stored]

end Itasca.Runtime.Code
