import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulEmission
import Itasca.Runtime.Compiler.Local.Relations.Instructions.ScalarEmissionAcceptance

/-!
References, memory metadata, and bulk operations satisfy the local checker from source signatures, operand capacities, and exact immutable pair entries.

Main declarations: `StatefulEmission.instructions_accept` and `IndirectCallEmission.instructions_accept`. A direct consumer is `Compiler.Body.Relations.Checking.ExecutableInstructionAcceptance`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private theorem width_reference (ty : reftype) : width (valtype_reftype ty) = 1 := by
  cases ty <;> rfl

macro "stateful_capacity " inputs:ident outputs:ident second:ident pair:ident : tactic => `(tactic|
  (simp only [slots_append,slots,width_reference,show width .I32 = 1 from rfl,show width .FUNCREF = 1 from rfl,
     Abs.Stateful.Instruction.arity,StatefulPair] at $inputs $outputs $second $pair
   try have secondPosition := $second (by decide)
   first | exact (List.getElem?_eq_some_iff.mp $pair).1 | omega))

/-- References, memory metadata, and bulk operations satisfy the local checker
from source signatures, operand capacities, and exact immutable pair entries. -/
theorem StatefulEmission.instructions_accept {pairs C before source emitted after}
    (emission : StatefulEmission pairs C before source emitted after)
    (function : runtime.bytecode.CompiledFunction) (table : pairs = function.indirect.val)
    (inputs : slots C.LOCALS+slots before ≤ function.slot_count.val)
    (outputs : slots C.LOCALS+slots after ≤ function.slot_count.val) :
    ∀ instruction ∈ emitted,
      runtime.bytecode.CompiledFunction.instruction_valid function instruction = .ok true := by
  cases emission with
  | instruction stack input output op signature first second a b entry firstSlot secondSlot arguments pair =>
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    rw [table] at pair
    cases signature with
    | refNull => apply CoreInstructionBounds.accepts (.refNull ?_) <;> stateful_capacity inputs outputs secondSlot pair
    | refFunc => apply CoreInstructionBounds.accepts (.refFunc ?_) <;> stateful_capacity inputs outputs secondSlot pair
    | refIsNull => apply CoreInstructionBounds.accepts (.refIsNull ?_ ?_) <;> stateful_capacity inputs outputs secondSlot pair
    | tableGet => apply CoreInstructionBounds.accepts (.tableGet ?_ ?_) <;> stateful_capacity inputs outputs secondSlot pair
    | tableSet => apply CoreInstructionBounds.accepts (.tableSet ?_ ?_) <;> stateful_capacity inputs outputs secondSlot pair
    | tableSize => apply CoreInstructionBounds.accepts (.tableSize ?_) <;> stateful_capacity inputs outputs secondSlot pair
    | tableGrow => apply CoreInstructionBounds.accepts (.tableGrow ?_) <;> stateful_capacity inputs outputs secondSlot pair
    | tableFill => apply CoreInstructionBounds.accepts (.tableFill ?_) <;> stateful_capacity inputs outputs secondSlot pair
    | tableCopy => apply CoreInstructionBounds.accepts (.tableCopy ?_ ?_) <;> stateful_capacity inputs outputs secondSlot pair
    | tableInit => apply CoreInstructionBounds.accepts (.tableInit ?_ ?_) <;> stateful_capacity inputs outputs secondSlot pair
    | elemDrop => exact CoreInstructionBounds.accepts .elemDrop
    | memorySize => apply CoreInstructionBounds.accepts (.memorySize ?_) <;> stateful_capacity inputs outputs secondSlot pair
    | memoryGrow => apply CoreInstructionBounds.accepts (.memoryGrow ?_) <;> stateful_capacity inputs outputs secondSlot pair
    | memoryFill => apply CoreInstructionBounds.accepts (.memoryFill ?_) <;> stateful_capacity inputs outputs secondSlot pair
    | memoryCopy => apply CoreInstructionBounds.accepts (.memoryCopy ?_) <;> stateful_capacity inputs outputs secondSlot pair
    | memoryInit => apply CoreInstructionBounds.accepts (.memoryInit ?_) <;> stateful_capacity inputs outputs secondSlot pair
    | dataDrop => exact CoreInstructionBounds.accepts .dataDrop

/-- Indirect calls check their selector, argument base, and captured pair index.
The source signature and table type remain in the emission record. -/
theorem IndirectCallEmission.instructions_accept {pairs C before source emitted after}
    (emission : IndirectCallEmission pairs C before source emitted after)
    (function : runtime.bytecode.CompiledFunction) (table : pairs = function.indirect.val)
    (inputs : slots C.LOCALS+slots before ≤ function.slot_count.val) :
    ∀ instruction ∈ emitted,
      runtime.bytecode.CompiledFunction.instruction_valid function instruction = .ok true := by
  cases emission with
  | call front params results typeIndex tableIndex entry index base bounds signature selected pair basePosition indexPosition =>
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    have row := (List.getElem?_eq_some_iff.mp pair).1
    rw [table] at row
    simp only [slots_append,slots,width] at inputs
    apply CoreInstructionBounds.accepts (.callIndirect ?_ ?_ ?_)
    · omega
    · omega
    · exact row

end Itasca.Runtime.Code
