import Itasca.Runtime.Compiler.Local.Relations.Instructions.WellFormedTotal
import Itasca.Runtime.Compiler.Local.Relations.Instructions.InstructionCheckAcceptance
import Itasca.Runtime.Compiler.Local.Capacity.IndependentBodyReplay
import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericInstructionPublication
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Runtime.Compiler.Local.Lowering.Float.FloatInstructionPublication
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulLowered

/-!
Sections, each formerly its own module: SimdInstructionAcceptance, LinearInstructionAcceptance, ScalarEmissionAcceptance, StatefulInstructionAcceptance, WellFormedAcceptance.
-/

/-! ## SimdInstructionAcceptance -/

section

/-!
SIMD checking accepts from the independently selected opcode shape, concrete input/output slot widths, and immediate-table membership.

Main declarations: `simd_instruction_accepts` and `simd_instruction_monotone`. A direct consumer is `Compiler.Local.Checking.OpenInstructionCompiler`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- SIMD checking accepts from the independently selected opcode shape,
concrete input/output slot widths, and immediate-table membership. -/
theorem simd_instruction_accepts (function : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) (opcode dst input entry x y z output : U32)
    (projected : runtime.bytecode.Instr.simd instruction = .ok (some (opcode,dst,input,entry)))
    (shape : runtime.bytecode.simd_shape opcode = .ok (some (x,y,z,output)))
    (inputs : input.val+x.val+y.val+z.val ≤ function.slot_count.val)
    (destination : dst.val+output.val ≤ function.slot_count.val)
    (immediate : entry.val < function.simd.length) :
    runtime.bytecode.CompiledFunction.instruction_valid function instruction = .ok true := by
  obtain ⟨scalar,load,store⟩ := simd_view_disjoint instruction opcode dst input entry projected
  have accepted : runtime.bytecode.CompiledFunction.instruction_valid function instruction ⦃ result => result = true ⦄ := by
    unfold runtime.bytecode.CompiledFunction.instruction_valid
    simp only [scalar,load,store,projected,shape,bind_ok,uncurry_apply_pair]
    step as ⟨xy,xyEq⟩
    step as ⟨xyz,xyzEq⟩
    rw [slots_fit_accepts function input xyz (by scalar_tac)]
    simp only [bind_ok,↓reduceIte]
    rw [slots_fit_accepts function dst output destination]
    simp only [bind_ok,↓reduceIte,lift]
    simp only [bind_ok,WP.spec_ok,decide_eq_true_eq]
    scalar_tac
  obtain ⟨result,called,rfl⟩ := WP.spec_imp_exists accepted
  exact called

/-- Later emission, slot observations, and SIMD-table appends retain checking
of an earlier SIMD instruction. -/
theorem simd_instruction_monotone (before after : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) (opcode dst input entry : U32)
    (projected : runtime.bytecode.Instr.simd instruction = .ok (some (opcode,dst,input,entry)))
    (capacity : before.slot_count.val ≤ after.slot_count.val)
    (table : before.simd.length ≤ after.simd.length)
    (accepted : runtime.bytecode.CompiledFunction.instruction_valid before instruction = .ok true) :
    runtime.bytecode.CompiledFunction.instruction_valid after instruction = .ok true := by
  obtain ⟨scalar,load,store⟩ := simd_view_disjoint instruction opcode dst input entry projected
  have called := accepted
  unfold runtime.bytecode.CompiledFunction.instruction_valid at called
  simp only [scalar,load,store,projected,bind_ok,uncurry_apply_pair] at called
  obtain ⟨shape,shapeRun,rest⟩ := bind_ok_inv _ _ _ called
  cases shape with
  | none => simp at rest
  | some shape =>
    obtain ⟨x,y,z,output⟩ := shape
    have bounds := simd_valid_bounds before instruction opcode dst input entry x y z output projected shapeRun accepted
    exact simd_instruction_accepts after instruction opcode dst input entry x y z output projected shapeRun
      (by omega) (by omega) (by omega)

end Itasca.Runtime.Compiler

end

/-! ## LinearInstructionAcceptance -/

section

/-!
A typed local transfer fits whether the value occupies one word or two.

Main declarations: `move_instruction_accepts` and `LinearEmission.instructions_accept`. A direct consumer is `Compiler.Local.Relations.Instructions.ScalarEmissionAcceptance`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- A typed local transfer fits whether the value occupies one word or two. -/
theorem move_instruction_accepts (function : runtime.bytecode.CompiledFunction) (ty : valtype) (dst src : U32)
    (destination : dst.val+width ty ≤ function.slot_count.val)
    (source : src.val+width ty ≤ function.slot_count.val) :
    runtime.bytecode.CompiledFunction.instruction_valid function (move ty dst src) = .ok true := by
  have widths : width ty = 1 ∨ width ty = 2 := by cases ty <;> decide
  rcases widths with one | two
  · simp only [move,one,Nat.reduceEqDiff,↓reduceIte]
    exact (CoreInstructionBounds.copy (by omega) (by omega)).accepts
  · simp only [move,two,↓reduceIte]
    exact (CoreInstructionBounds.copy2 (by omega) (by omega)).accepts

/-- Source-indexed literal emissions pass the actual bytecode checker when
both source stack boundaries fit. This checks every emitted bytecode word,
independently of any semantic reachability in the completed function. -/
theorem LinearEmission.instructions_accept {locals before source emitted after}
    (emission : LinearEmission locals before source emitted after)
    (function : runtime.bytecode.CompiledFunction)
    (inputs : slots locals+slots before ≤ function.slot_count.val)
    (outputs : slots locals+slots after ≤ function.slot_count.val) :
    ∀ instruction ∈ emitted,
      runtime.bytecode.CompiledFunction.instruction_valid function instruction = .ok true := by
  cases emission with
  | nop | drop => simp
  | const32 stack dst word position =>
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    apply CoreInstructionBounds.accepts (.const32 _)
    simp only [slots_append,slots,width] at outputs
    omega
  | const64 stack dst word position =>
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    apply CoreInstructionBounds.accepts (.const64 _)
    simp only [slots_append,slots,width] at outputs
    omega
  | binary stack ty op left right first second =>
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    have bound : right.val+1 ≤ function.slot_count.val := by
      cases ty <;> simp [integerType,slots_append,slots,width] at inputs <;> omega
    have firstBound : left.val+1 ≤ function.slot_count.val := by omega
    cases ty <;> cases op
    all_goals apply scalar_instruction_accepts function _ _ _ _ _ rfl firstBound firstBound bound
  | numeric stack op left right first second =>
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    exact numeric_instruction_accepts function locals stack op left right first second inputs
  | eqz32 stack operand position =>
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    have bound : operand.val+1 ≤ function.slot_count.val := by
      simp only [slots_append,slots,width] at inputs
      omega
    exact scalar_instruction_accepts function _ 69#u16 operand operand operand rfl bound bound bound
  | eqz64 stack operand position =>
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    have bound : operand.val+1 ≤ function.slot_count.val := by
      simp only [slots_append,slots,width] at inputs
      omega
    exact scalar_instruction_accepts function _ 80#u16 operand operand operand rfl bound bound bound
  | localGet stack ty index localSlot stackSlot localType localPos stackPos =>
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    have localBound := offset_add_width_le localType
    simp only [slots_append,slots] at outputs
    apply move_instruction_accepts function ty stackSlot localSlot <;> omega
  | localSet stack ty index localSlot stackSlot localType localPos stackPos =>
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    have localBound := offset_add_width_le localType
    simp only [slots_append,slots] at inputs
    apply move_instruction_accepts function ty localSlot stackSlot <;> omega
  | localTee stack ty index localSlot stackSlot localType localPos stackPos =>
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    have localBound := offset_add_width_le localType
    simp only [slots_append,slots] at inputs
    apply move_instruction_accepts function ty localSlot stackSlot <;> omega

end Itasca.Runtime.Compiler

end

/-! ## ScalarEmissionAcceptance -/

section

/-!
Complete scalar memory, global, select, literal and float emission checking from source stack capacities. Environment typing remains in the independent emission record and is not replaced with successful compiler checking.

Main declarations: `ScalarEmission.instructions_accept`. A direct consumer is `Compiler.Local.Relations.Instructions.StatefulInstructionAcceptance`.
-/

namespace Itasca.Runtime.Compiler
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
    (op : SourceMachine.Memory.Load) (dst address offset : U32)
    (destination : dst.val+1 ≤ function.slot_count.val) (source : address.val+1 ≤ function.slot_count.val) :
    runtime.bytecode.CompiledFunction.instruction_valid function (memoryLoadInstruction op dst address offset) = .ok true := by
  cases op with
  | full ty => cases ty <;> exact load_instruction_accepts function _ _ dst address offset rfl rfl destination source
  | packed ty width sign => cases ty <;> cases width <;> cases sign <;>
      exact load_instruction_accepts function _ _ dst address offset rfl rfl destination source

private theorem memory_store_instruction_accepts (function : runtime.bytecode.CompiledFunction)
    (op : SourceMachine.Memory.Store) (address value offset : U32)
    (first : address.val+1 ≤ function.slot_count.val) (second : value.val+1 ≤ function.slot_count.val) :
    runtime.bytecode.CompiledFunction.instruction_valid function (memoryStoreInstruction op address value offset) = .ok true := by
  cases op with
  | full ty => cases ty <;> exact store_instruction_accepts function _ _ address value offset rfl rfl rfl first second
  | packed ty width => cases ty <;> cases width <;>
      exact store_instruction_accepts function _ _ address value offset rfl rfl rfl first second

/-- Complete scalar memory, global, select, literal and float emission checking from
source stack capacities. Environment typing remains in the independent emission
record and is not replaced with successful compiler checking. -/
theorem ScalarEmission.instructions_accept {C before source emitted after}
    (emission : ScalarEmission C before source emitted after)
    (function : runtime.bytecode.CompiledFunction)
    (inputs : slots C.LOCALS+slots before ≤ function.slot_count.val)
    (outputs : slots C.LOCALS+slots after ≤ function.slot_count.val) :
    ∀ instruction ∈ emitted,
      runtime.bytecode.CompiledFunction.instruction_valid function instruction = .ok true := by
  cases emission with
  | linear head => exact head.instructions_accept function inputs outputs
  | float stack op left right first second =>
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    exact float_instruction_accepts function C.LOCALS stack op left right first second inputs
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

end Itasca.Runtime.Compiler

end

/-! ## StatefulInstructionAcceptance -/

section

/-!
References, memory metadata, and bulk operations satisfy the local checker from source signatures, operand capacities, and exact immutable pair entries.

Main declarations: `StatefulEmission.instructions_accept` and `IndirectCallEmission.instructions_accept`. A direct consumer is `Compiler.Body.Relations.Checking.ExecutableInstructionAcceptance`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

private theorem width_reference (ty : reftype) : width (valtype_reftype ty) = 1 := by
  cases ty <;> rfl

macro "stateful_capacity " inputs:ident outputs:ident second:ident pair:ident : tactic => `(tactic|
  (simp only [slots_append,slots,width_reference,show width .I32 = 1 from rfl,show width .FUNCREF = 1 from rfl,
     SourceMachine.Stateful.Instruction.arity,StatefulPair] at $inputs $outputs $second $pair
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

end Itasca.Runtime.Compiler

end

/-! ## WellFormedAcceptance -/

section

/-! Acceptance directions for the structural publication checker. Component
validity is a local obligation to derive from emitted code and source bounds;
no complete-module compilation success is assumed by these helper lemmas. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std


end Itasca.Runtime.Compiler

end
