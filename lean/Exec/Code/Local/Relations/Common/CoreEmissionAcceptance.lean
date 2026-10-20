import Exec.Code.Local.Relations.Common.LinearInstructionAcceptance
import Exec.Code.Local.Relations.Common.CoreEmission

namespace Exec.Code
open Aeneas Aeneas.Std

private theorem global_get_instruction_accepts (function : runtime.bytecode.CompiledFunction)
    (ty : valtype) (dst index : U32) (bound : dst.val+width ty ≤ function.slot_count.val) :
    runtime.bytecode.CompiledFunction.instruction_valid function (globalGetInstruction (decide (width ty = 2)) dst index) = .ok true := by
  cases ty <;> simp only [width] at bound ⊢
  all_goals first
    | exact (CoreInstructionBounds.globalGet bound).accepts
    | exact (CoreInstructionBounds.globalGet2 bound).accepts

private theorem global_set_instruction_accepts (function : runtime.bytecode.CompiledFunction)
    (ty : valtype) (src index : U32) (bound : src.val+width ty ≤ function.slot_count.val) :
    runtime.bytecode.CompiledFunction.instruction_valid function (globalSetInstruction (decide (width ty = 2)) src index) = .ok true := by
  cases ty <;> simp only [width] at bound ⊢
  all_goals first
    | exact (CoreInstructionBounds.globalSet bound).accepts
    | exact (CoreInstructionBounds.globalSet2 bound).accepts

private theorem select_instruction_accepts (function : runtime.bytecode.CompiledFunction)
    (ty : valtype) (left right condition : U32)
    (first : left.val+width ty ≤ function.slot_count.val)
    (second : right.val+width ty ≤ function.slot_count.val)
    (test : condition.val+1 ≤ function.slot_count.val) :
    runtime.bytecode.CompiledFunction.instruction_valid function (selectInstruction (decide (width ty = 2)) left right condition) = .ok true := by
  cases ty <;> simp only [width] at first second ⊢
  all_goals first
    | exact (CoreInstructionBounds.select first second test).accepts
    | exact (CoreInstructionBounds.select2 first second test).accepts

private theorem memory_load_instruction_accepts (function : runtime.bytecode.CompiledFunction)
    (op : Abs.Memory.Load) (dst address offset : U32)
    (destination : dst.val+1 ≤ function.slot_count.val) (source : address.val+1 ≤ function.slot_count.val) :
    runtime.bytecode.CompiledFunction.instruction_valid function (memoryLoadInstruction op dst address offset) = .ok true := by
  cases op with
  | full ty => cases ty <;> exact load_instruction_accepts function _ _ dst address offset rfl rfl destination source
  | packed ty width sign => cases ty <;> cases width <;> cases sign <;>
      exact load_instruction_accepts function _ _ dst address offset rfl rfl destination source

private theorem memory_store_instruction_accepts (function : runtime.bytecode.CompiledFunction)
    (op : Abs.Memory.Store) (address value offset : U32)
    (first : address.val+1 ≤ function.slot_count.val) (second : value.val+1 ≤ function.slot_count.val) :
    runtime.bytecode.CompiledFunction.instruction_valid function (memoryStoreInstruction op address value offset) = .ok true := by
  cases op with
  | full ty => cases ty <;> exact store_instruction_accepts function _ _ address value offset rfl rfl rfl first second
  | packed ty width => cases ty <;> cases width <;>
      exact store_instruction_accepts function _ _ address value offset rfl rfl rfl first second

/-- Complete scalar memory, global, select, and literal emission checking from
source stack capacities. Environment typing remains in the independent emission
record and is not replaced with successful compiler checking. -/
theorem CoreEmission.instructions_accept {C before source emitted after}
    (emission : CoreEmission C before source emitted after)
    (function : runtime.bytecode.CompiledFunction)
    (inputs : slots C.LOCALS+slots before ≤ function.slot_count.val)
    (outputs : slots C.LOCALS+slots after ≤ function.slot_count.val) :
    ∀ instruction ∈ emitted,
      runtime.bytecode.CompiledFunction.instruction_valid function instruction = .ok true := by
  cases emission with
  | pure head => exact head.instructions_accept function inputs outputs
  | float32 stack dst bits position =>
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    apply CoreInstructionBounds.accepts (.const32 _)
    simp only [slots_append,slots,width] at outputs
    omega
  | float64 stack dst bits position =>
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    apply CoreInstructionBounds.accepts (.const64 _)
    simp only [slots_append,slots,width] at outputs
    omega
  | select stack ty left right condition first second test =>
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    have positive := width_positive ty
    simp only [slots_append,slots,show width .I32 = 1 from rfl] at inputs
    apply select_instruction_accepts function ty left right condition <;> omega
  | globalGet stack mutability ty index dst globalType position =>
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    simp only [slots_append,slots] at outputs
    apply global_get_instruction_accepts function ty dst index
    omega
  | globalSet stack ty index src globalType position =>
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    simp only [slots_append,slots] at inputs
    apply global_set_instruction_accepts function ty src index
    omega
  | load stack op argument address offset memory available sourceOffset position =>
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    simp only [slots_append,slots,width] at inputs
    apply memory_load_instruction_accepts function op address address offset <;> omega
  | store stack op argument address value offset memory available sourceOffset first second =>
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    have one : width (valtype_numtype op.type) = 1 := by cases op.type <;> rfl
    simp only [slots_append,slots,one,show width .I32 = 1 from rfl] at inputs
    apply memory_store_instruction_accepts function op address value offset <;> omega

end Exec.Code
