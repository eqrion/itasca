import Itasca.Runtime.Equations.Bytecode
import Itasca.Generated.Funs
import Itasca.Support.Translation
import Mathlib.Tactic.IntervalCases

/-!
Proofs for Runtime / Compiler / Local / Relations / Instructions.

This module collects InstructionCheckAcceptance, WellFormedTotal.
Each section documents its contracts and consumers.
-/

/-! ## InstructionCheckAcceptance -/

section

/-! ## WellFormed -/

section

/-!
Instruction-check loops and compiled-function well-formedness.

Main declarations: `checkInstructionBody` and `checkInstructions`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation

abbrev checkInstructionBody (f : runtime.bytecode.CompiledFunction)
    (length : Usize) (synthetic valid : Bool) (index : Usize) :=
  runtime.bytecode.CompiledFunction.well_formed_loop0.body f.locals f.local_slots f.param_slots
    f.slot_count f.max_stack f.code f.jump_tables f.v128_pool f.indirect f.simd f.source_offsets
    f.controls f.type_index f.body_start f.body_end length synthetic valid index

abbrev checkInstructions (f : runtime.bytecode.CompiledFunction)
    (length : Usize) (synthetic valid : Bool) (index : Usize) :=
  runtime.bytecode.CompiledFunction.well_formed_loop0 f.locals f.local_slots f.param_slots
    f.slot_count f.max_stack f.code f.jump_tables f.v128_pool f.indirect f.simd f.source_offsets
    f.controls f.type_index f.body_start f.body_end length synthetic valid index

/-- A successful check iteration records the actual instruction-validity
result and advances the bounded counter. -/
theorem check_instruction_body_cont (f : runtime.bytecode.CompiledFunction)
    (length : Usize) (synthetic valid nextValid : Bool) (index nextIndex : Usize)
    (lengthEq : length.val = f.code.length)
    (run : checkInstructionBody f length synthetic valid index = .ok (.cont (nextValid, nextIndex))) :
    index.val < length.val ∧ valid = true ∧ nextIndex.val = index.val + 1 ∧
      (nextValid = true → ∃ instruction,
        f.code.val[index.val]? = some instruction ∧
        runtime.bytecode.CompiledFunction.instruction_valid f instruction = .ok true) := by
  unfold checkInstructionBody runtime.bytecode.CompiledFunction.well_formed_loop0.body at run
  split at run
  · rename_i bounded
    split at run
    · rename_i validTrue
      obtain ⟨sourceValid, checkedSource, run⟩ := bind_ok_inv _ _ _ run
      obtain ⟨instruction, fetched, run⟩ := bind_ok_inv _ _ _ run
      obtain ⟨instructionValid, checked, run⟩ := bind_ok_inv _ _ _ run
      obtain ⟨accepted, chosen, run⟩ := bind_ok_inv _ _ _ run
      obtain ⟨advanced, incremented, run⟩ := bind_ok_inv _ _ _ run
      have same : (accepted, advanced) = (nextValid, nextIndex) := by
        exact ControlFlow.cont.inj (Result.ok_injective run)
      cases same
      refine ⟨by scalar_tac, validTrue, ?_, ?_⟩
      · have h := Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac)
        rw [incremented] at h
        simpa using h
      · intro acceptedTrue
        have checkedTrue : instructionValid = true := by
          cases instructionValid with
          | false => simp only [Bool.false_eq_true, ite_false] at chosen; have h := Result.ok_injective chosen; simp_all
          | true => rfl
        refine ⟨instruction, ?_, checkedTrue ▸ checked⟩
        have indexBound : index.val < f.code.length := by scalar_tac
        have lookup : alloc.vec.Vec.index_usize f.code index
            ⦃ out => f.code.val[index.val]? = some out ⦄ := by
          step as ⟨out, hout⟩
          rw [List.getElem?_eq_getElem indexBound, hout]
        change alloc.vec.Vec.index_usize f.code index = .ok instruction at fetched
        rw [fetched] at lookup
        simpa only [WP.spec_ok] using lookup
    · cases Result.ok_injective run
  · cases Result.ok_injective run

theorem check_instruction_body_done (f : runtime.bytecode.CompiledFunction)
    (length : Usize) (synthetic valid : Bool) (index : Usize)
    (run : checkInstructionBody f length synthetic valid index = .ok (.done true)) :
    length.val ≤ index.val ∧ valid = true := by
  cases valid with
  | false =>
    simp [checkInstructionBody, runtime.bytecode.CompiledFunction.well_formed_loop0.body] at run
  | true =>
    unfold checkInstructionBody runtime.bytecode.CompiledFunction.well_formed_loop0.body at run
    by_cases bounded : index < length
    · simp only [if_pos bounded, ite_true] at run
      obtain ⟨sourceValid, checkedSource, run⟩ := bind_ok_inv _ _ _ run
      obtain ⟨instruction, fetched, run⟩ := bind_ok_inv _ _ _ run
      obtain ⟨instructionValid, checked, run⟩ := bind_ok_inv _ _ _ run
      obtain ⟨accepted, chosen, run⟩ := bind_ok_inv _ _ _ run
      obtain ⟨advanced, incremented, run⟩ := bind_ok_inv _ _ _ run
      cases Result.ok_injective run
    · exact ⟨by scalar_tac, rfl⟩

/-- Successful observed checking validates every remaining instruction. The
proof follows the extracted counter loop, without assuming its termination or
that instruction validation itself succeeds on arbitrary malformed input. -/
theorem check_instructions_valid (f : runtime.bytecode.CompiledFunction)
    (length : Usize) (synthetic valid : Bool) (index : Usize)
    (lengthEq : length.val = f.code.length)
    (run : checkInstructions f length synthetic valid index = .ok true) :
    valid = true ∧ ∀ j, index.val ≤ j → j < length.val → ∃ instruction,
      f.code.val[j]? = some instruction ∧
      runtime.bytecode.CompiledFunction.instruction_valid f instruction = .ok true := by
  have main : ∀ n (index : Usize) (valid : Bool), n = length.val - index.val →
      checkInstructions f length synthetic valid index = .ok true →
      valid = true ∧ ∀ j, index.val ≤ j → j < length.val → ∃ instruction,
        f.code.val[j]? = some instruction ∧
        runtime.bytecode.CompiledFunction.instruction_valid f instruction = .ok true := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro index valid measure run
      unfold checkInstructions runtime.bytecode.CompiledFunction.well_formed_loop0 at run
      rw [loop.eq_def] at run
      obtain ⟨flow, checked, rest⟩ := bind_ok_inv _ _ _ run
      cases flow with
      | done result =>
        have same : result = true := Result.ok_injective rest
        subst result
        have terminal := check_instruction_body_done f length synthetic valid index checked
        refine ⟨terminal.2, ?_⟩
        intro j lower upper
        omega
      | cont state =>
        rcases state with ⟨nextValid, nextIndex⟩
        have advanced := check_instruction_body_cont f length synthetic valid nextValid index nextIndex lengthEq checked
        have smaller : length.val - nextIndex.val < n := by omega
        have remaining := ih _ smaller nextIndex nextValid rfl rest
        have current := advanced.2.2.2 remaining.1
        refine ⟨advanced.2.1, ?_⟩
        intro j lower upper
        by_cases same : j = index.val
        · subst j; exact current
        · exact remaining.2 j (by omega) upper
  exact main _ index valid rfl run

theorem check_jump_table_false (values : alloc.vec.Vec U32) (length index : Usize) :
    runtime.bytecode.CompiledFunction.well_formed_loop1 values length false index = .ok false := by
  unfold runtime.bytecode.CompiledFunction.well_formed_loop1
  rw [loop.eq_def]
  simp only [runtime.bytecode.CompiledFunction.well_formed_loop1.body]
  split <;> simp

theorem check_controls_false (values : alloc.vec.Vec runtime.compiler.ControlMap)
    (start stop length index : Usize) :
    runtime.bytecode.CompiledFunction.well_formed_loop2 values start stop length false index = .ok false := by
  unfold runtime.bytecode.CompiledFunction.well_formed_loop2
  rw [loop.eq_def]
  simp only [runtime.bytecode.CompiledFunction.well_formed_loop2.body]
  split <;> simp

theorem check_jump_table_true (values : alloc.vec.Vec U32) (length index : Usize) (valid : Bool)
    (run : runtime.bytecode.CompiledFunction.well_formed_loop1 values length valid index = .ok true) :
    valid = true := by
  cases valid with
  | false => rw [check_jump_table_false] at run; cases Result.ok_injective run
  | true => rfl

theorem check_controls_true (values : alloc.vec.Vec runtime.compiler.ControlMap)
    (start stop length index : Usize) (valid : Bool)
    (run : runtime.bytecode.CompiledFunction.well_formed_loop2 values start stop length valid index = .ok true) :
    valid = true := by
  cases valid with
  | false => rw [check_controls_false] at run; cases Result.ok_injective run
  | true => rfl

/-- Later jump-table/control checks cannot turn failed instruction validation
back into successful compilation. -/
theorem checked_tail (f : runtime.bytecode.CompiledFunction) (length : Usize) (synthetic : Bool)
    (lengthEq : length.val = f.code.length)
    (run : (do
      let valid ← checkInstructions f length synthetic true 0#usize
      let valid' ← runtime.bytecode.CompiledFunction.well_formed_loop1 f.jump_tables length valid 0#usize
      runtime.bytecode.CompiledFunction.well_formed_loop2 f.controls f.body_start f.body_end length valid' 0#usize) = .ok true) :
    ∀ j, j < f.code.length → ∃ instruction, f.code.val[j]? = some instruction ∧
      runtime.bytecode.CompiledFunction.instruction_valid f instruction = .ok true := by
  obtain ⟨valid, instructions, run⟩ := bind_ok_inv _ _ _ run
  obtain ⟨valid', jumps, controls⟩ := bind_ok_inv _ _ _ run
  have controlTrue := check_controls_true _ _ _ _ _ _ controls
  subst valid'
  have jumpsTrue := check_jump_table_true _ _ _ _ jumps
  subst valid
  have checked := check_instructions_valid f length synthetic true 0#usize lengthEq instructions
  intro j bound
  exact checked.2 j (by scalar_tac) (by omega)

/-- Publishing through the actual structural gate guarantees every retained
instruction passed its own concrete bounds check. -/
theorem well_formed_instructions (f : runtime.bytecode.CompiledFunction)
    (run : runtime.bytecode.CompiledFunction.well_formed f = .ok true) :
    ∀ j, j < f.code.length → ∃ instruction, f.code.val[j]? = some instruction ∧
      runtime.bytecode.CompiledFunction.instruction_valid f instruction = .ok true := by
  unfold runtime.bytecode.CompiledFunction.well_formed at run
  obtain ⟨synthetic, syntheticCheck, run⟩ := bind_ok_inv _ _ _ run
  dsimp only at run
  repeat' first
    | exact checked_tail f (alloc.vec.Vec.len f.code) synthetic rfl run
    | (have impossible := Result.ok_injective run; contradiction)
    | split at run
    | obtain ⟨value, checked, run⟩ := bind_ok_inv _ _ _ run

theorem well_formed_fetched (f : runtime.bytecode.CompiledFunction)
    (run : runtime.bytecode.CompiledFunction.well_formed f = .ok true)
    (pc : Nat) (instruction : runtime.bytecode.Instr)
    (fetched : f.code.val[pc]? = some instruction) :
    runtime.bytecode.CompiledFunction.instruction_valid f instruction = .ok true := by
  obtain ⟨actual, found, checked⟩ := well_formed_instructions f run pc
    (List.getElem?_eq_some_iff.mp fetched |>.1)
  have same : actual = instruction := Option.some.inj (found.symm.trans fetched)
  exact same ▸ checked

end Itasca.Compiler

end

/-! ## SlotCheckAcceptance -/

section

/-!
Exact arithmetic acceptance of the concrete slot-range check. The upper bound is expressed in natural coordinates, avoiding unsigned subtraction.

Main declarations: `slots_fit_accepts`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Exact arithmetic acceptance of the concrete slot-range check. The upper
bound is expressed in natural coordinates, avoiding unsigned subtraction. -/
theorem slots_fit_accepts (function : runtime.bytecode.CompiledFunction) (start count : U32)
    (inside : start.val+count.val ≤ function.slot_count.val) :
    runtime.bytecode.CompiledFunction.slots_fit function start count = .ok true := by
  have lower : start ≤ function.slot_count := by scalar_tac
  have accepted : runtime.bytecode.CompiledFunction.slots_fit function start count ⦃ result => result = true ⦄ := by
    unfold runtime.bytecode.CompiledFunction.slots_fit
    simp only [if_pos lower]
    step as ⟨remaining,subtracted⟩
    have fits : count ≤ remaining := by scalar_tac
    simp [fits]
  obtain ⟨result,called,rfl⟩ := WP.spec_imp_exists accepted
  exact called

end Itasca.Compiler

end

/-! ## CoreInstructionAcceptance -/

section

/-!
Numerical publication obligations for non-projected bytecode forms. Global/function indices are checked by execution against its environment; the local bytecode checker checks slots and its own function-local table indices.

Main declarations: `CoreInstructionBounds`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Numerical publication obligations for non-projected bytecode forms.
Global/function indices are checked by execution against its environment; the
local bytecode checker checks slots and its own function-local table indices. -/
inductive CoreInstructionBounds (function : runtime.bytecode.CompiledFunction) : runtime.bytecode.Instr → Prop
  | copy {dst src : U32} (slot0 : dst.val+1 ≤ function.slot_count.val) (slot1 : src.val+1 ≤ function.slot_count.val) : CoreInstructionBounds function (.Copy dst src)
  | copy2 {dst src : U32} (slot0 : dst.val+2 ≤ function.slot_count.val) (slot1 : src.val+2 ≤ function.slot_count.val) : CoreInstructionBounds function (.Copy2 dst src)
  | copyN {dst src count : U32} (slot0 : dst.val+count.val ≤ function.slot_count.val) (slot1 : src.val+count.val ≤ function.slot_count.val) (bound0 : dst.val ≤ src.val) : CoreInstructionBounds function (.CopyN dst src count)
  | const32 {dst value : U32} (slot0 : dst.val+1 ≤ function.slot_count.val) : CoreInstructionBounds function (.Const32 dst value)
  | const64 {dst : U32} {value64 : U64} (slot0 : dst.val+1 ≤ function.slot_count.val) : CoreInstructionBounds function (.Const64 dst value64)
  | constV128 {dst entry : U32} (slot0 : dst.val+2 ≤ function.slot_count.val) (bound0 : entry.val < function.v128_pool.length) : CoreInstructionBounds function (.ConstV128 dst entry)
  | jump {target : U32} (bound0 : target.val < function.code.length) : CoreInstructionBounds function (.Jump target)
  | jumpIfZero {cond target : U32} (slot0 : cond.val+1 ≤ function.slot_count.val) (bound0 : target.val < function.code.length) : CoreInstructionBounds function (.JumpIfZero cond target)
  | jumpIfNonZero {cond target : U32} (slot0 : cond.val+1 ≤ function.slot_count.val) (bound0 : target.val < function.code.length) : CoreInstructionBounds function (.JumpIfNonZero cond target)
  | jumpTable {index start count : U32} (slot0 : index.val+1 ≤ function.slot_count.val) (bound0 : 0 < count.val) (bound1 : start.val+count.val ≤ function.jump_tables.length) : CoreInstructionBounds function (.JumpTable index start count)
  | loopHead : CoreInstructionBounds function (.LoopHead)
  | call {index base : U32} (slot0 : base.val+0 ≤ function.slot_count.val) : CoreInstructionBounds function (.Call index base)
  | callIndirect {entry index base : U32} (slot0 : base.val+0 ≤ function.slot_count.val) (slot1 : index.val+1 ≤ function.slot_count.val) (bound0 : entry.val < function.indirect.length) : CoreInstructionBounds function (.CallIndirect entry index base)
  | return_ {src count : U32} (slot0 : src.val+count.val ≤ function.slot_count.val) : CoreInstructionBounds function (.Return src count)
  | unreachable : CoreInstructionBounds function (.Unreachable)
  | select {left right cond : U32} (slot0 : left.val+1 ≤ function.slot_count.val) (slot1 : right.val+1 ≤ function.slot_count.val) (slot2 : cond.val+1 ≤ function.slot_count.val) : CoreInstructionBounds function (.Select left right cond)
  | select2 {left right cond : U32} (slot0 : left.val+2 ≤ function.slot_count.val) (slot1 : right.val+2 ≤ function.slot_count.val) (slot2 : cond.val+1 ≤ function.slot_count.val) : CoreInstructionBounds function (.Select2 left right cond)
  | globalGet {dst index : U32} (slot0 : dst.val+1 ≤ function.slot_count.val) : CoreInstructionBounds function (.GlobalGet dst index)
  | globalGet2 {dst index : U32} (slot0 : dst.val+2 ≤ function.slot_count.val) : CoreInstructionBounds function (.GlobalGet2 dst index)
  | globalSet {src index : U32} (slot0 : src.val+1 ≤ function.slot_count.val) : CoreInstructionBounds function (.GlobalSet src index)
  | globalSet2 {src index : U32} (slot0 : src.val+2 ≤ function.slot_count.val) : CoreInstructionBounds function (.GlobalSet2 src index)
  | memorySize {dst : U32} (slot0 : dst.val+1 ≤ function.slot_count.val) : CoreInstructionBounds function (.MemorySize dst)
  | memoryGrow {dst : U32} (slot0 : dst.val+1 ≤ function.slot_count.val) : CoreInstructionBounds function (.MemoryGrow dst)
  | memoryFill {dst : U32} (slot0 : dst.val+3 ≤ function.slot_count.val) : CoreInstructionBounds function (.MemoryFill dst)
  | memoryCopy {dst : U32} (slot0 : dst.val+3 ≤ function.slot_count.val) : CoreInstructionBounds function (.MemoryCopy dst)
  | memoryInit {dst index : U32} (slot0 : dst.val+3 ≤ function.slot_count.val) : CoreInstructionBounds function (.MemoryInit dst index)
  | dataDrop {index : U32} : CoreInstructionBounds function (.DataDrop index)
  | tableGet {dst index table : U32} (slot0 : dst.val+1 ≤ function.slot_count.val) (slot1 : index.val+1 ≤ function.slot_count.val) : CoreInstructionBounds function (.TableGet dst index table)
  | tableSet {index value table : U32} (slot0 : index.val+1 ≤ function.slot_count.val) (slot1 : value.val+1 ≤ function.slot_count.val) : CoreInstructionBounds function (.TableSet index value table)
  | tableSize {dst table : U32} (slot0 : dst.val+1 ≤ function.slot_count.val) : CoreInstructionBounds function (.TableSize dst table)
  | tableGrow {dst table : U32} (slot0 : dst.val+2 ≤ function.slot_count.val) : CoreInstructionBounds function (.TableGrow dst table)
  | tableFill {dst table : U32} (slot0 : dst.val+3 ≤ function.slot_count.val) : CoreInstructionBounds function (.TableFill dst table)
  | tableCopy {dst entry : U32} (slot0 : dst.val+3 ≤ function.slot_count.val) (bound0 : entry.val < function.indirect.length) : CoreInstructionBounds function (.TableCopy dst entry)
  | tableInit {dst entry : U32} (slot0 : dst.val+3 ≤ function.slot_count.val) (bound0 : entry.val < function.indirect.length) : CoreInstructionBounds function (.TableInit dst entry)
  | elemDrop {index : U32} : CoreInstructionBounds function (.ElemDrop index)
  | refNull {dst : U32} (slot0 : dst.val+1 ≤ function.slot_count.val) : CoreInstructionBounds function (.RefNull dst)
  | refIsNull {dst input : U32} (slot0 : dst.val+1 ≤ function.slot_count.val) (slot1 : input.val+1 ≤ function.slot_count.val) : CoreInstructionBounds function (.RefIsNull dst input)
  | refFunc {dst index : U32} (slot0 : dst.val+1 ≤ function.slot_count.val) : CoreInstructionBounds function (.RefFunc dst index)

private theorem checked_difference_accepts (length start count : Usize)
    (inside : start.val+count.val ≤ length.val) :
    (do let remaining ← length-start; Result.ok (decide (count ≤ remaining))) = .ok true := by
  have checked : (do let remaining ← length-start; Result.ok (decide (count ≤ remaining))) ⦃ result => result = true ⦄ := by
    step as ⟨remaining,difference⟩
    simp only [WP.spec_ok,decide_eq_true_eq]
    scalar_tac
  obtain ⟨result,called,rfl⟩ := WP.spec_imp_exists checked
  exact called

/-- Every core form satisfies the actual checker from its arithmetic bounds. -/
theorem CoreInstructionBounds.accepts {function : runtime.bytecode.CompiledFunction}
    {instruction : runtime.bytecode.Instr} (bounds : CoreInstructionBounds function instruction) :
    runtime.bytecode.CompiledFunction.instruction_valid function instruction = .ok true := by
  cases bounds
  all_goals simp only [runtime.bytecode.CompiledFunction.instruction_valid,
    runtime.bytecode.Instr.scalar,runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,
    runtime.bytecode.Instr.simd,runtime.bytecode.CompiledFunction.other_valid,bind_ok]
  all_goals repeat' first
    | rw [slots_fit_accepts _ _ _ (by scalar_tac)]
    | simp only [bind_ok,ite_true,lift]
  all_goals try split_ifs
  all_goals try simp_all only [Result.ok.injEq,decide_eq_true_eq,bind_ok]
  all_goals first | rfl | scalar_tac | (apply checked_difference_accepts; scalar_tac)

end Itasca.Compiler

end

/-! ## InstructionCheckAcceptance -/

section

/-!
Scalar operator checking accepts the exact projection supplied by lowering when its three concrete word slots fit the function's retained capacity.

Main declarations: `scalar_instruction_accepts` and `store_instruction_accepts`.
-/

namespace Itasca.Compiler
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

end Itasca.Compiler

end

end

/-! ## WellFormedTotal -/

section

/-! ## WellFormedTotal -/

section

/-!
Normal return of per-instruction validity checks and complete function well-formedness checks, including jump/control tables.
-/

/-! ## Instruction Projection Total -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
@[step] theorem slots_fit_total (f : runtime.bytecode.CompiledFunction) (start count : U32) :
    runtime.bytecode.CompiledFunction.slots_fit f start count ⦃ _ => True ⦄ := by
  unfold runtime.bytecode.CompiledFunction.slots_fit
  split <;> step*

@[step] theorem instruction_scalar_total (instruction : runtime.bytecode.Instr) :
    runtime.bytecode.Instr.scalar instruction ⦃ _ => True ⦄ := by
  cases instruction <;> exact (WP.spec_ok _).mpr True.intro

@[step] theorem instruction_load_total (instruction : runtime.bytecode.Instr) :
    runtime.bytecode.Instr.load instruction ⦃ _ => True ⦄ := by
  cases instruction <;> exact (WP.spec_ok _).mpr True.intro

@[step] theorem instruction_store_total (instruction : runtime.bytecode.Instr) :
    runtime.bytecode.Instr.store instruction ⦃ _ => True ⦄ := by
  cases instruction <;> exact (WP.spec_ok _).mpr True.intro

@[step] theorem instruction_simd_total (instruction : runtime.bytecode.Instr) :
    runtime.bytecode.Instr.simd instruction ⦃ result => match result with
      | none => True
      | some (op,_,_,_) => op.val < 256 ⦄ := by
  cases instruction <;> apply (WP.spec_ok _).mpr <;> dsimp only <;> decide

end Itasca.Compiler

end

/-! ## Instruction Validity Total -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
 @[step] theorem simd_shape_total (op : U32) (bound : op.val < 256) :
    runtime.bytecode.simd_shape op ⦃ result => match result with
      | none => True
      | some (a,b,c,d) => a.val ≤ 2 ∧ b.val ≤ 2 ∧ c.val ≤ 2 ∧ d.val ≤ 2 ⦄ := by
  rcases op with ⟨⟨n,hn⟩⟩
  change n < 256 at bound
  interval_cases n <;> with_unfolding_all
    (apply (WP.spec_ok _).mpr; first | exact True.intro | exact ⟨by decide, by decide, by decide, by decide⟩)

@[step] theorem other_valid_total (f : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) :
    runtime.bytecode.CompiledFunction.other_valid f instruction ⦃ _ => True ⦄ := by
  cases instruction <;> simp only [runtime.bytecode.CompiledFunction.other_valid, WP.spec_ok]
  all_goals step*

theorem instruction_valid_total (f : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) :
    runtime.bytecode.CompiledFunction.instruction_valid f instruction ⦃ _ => True ⦄ := by
  unfold runtime.bytecode.CompiledFunction.instruction_valid
  step as ⟨scalar, _⟩
  cases scalar with
  | some values =>
    rcases values with ⟨op, dst, a, b⟩
    simp only [bind_ok]
    step*
  | none =>
    simp only [bind_ok]
    step as ⟨load, _⟩
    cases load with
    | some values =>
      rcases values with ⟨op, dst, addr, offset⟩
      simp only [bind_ok]
      step*
    | none =>
      simp only [bind_ok]
      step as ⟨store, _⟩
      cases store with
      | some values =>
        rcases values with ⟨op, addr, value, offset⟩
        simp only [bind_ok]
        step*
      | none =>
        simp only [bind_ok]
        step as ⟨simd, opcodeBound⟩
        cases simd with
        | some values =>
          rcases values with ⟨op, dst, a, entry⟩
          simp only [bind_ok]
          step with simd_shape_total op opcodeBound as ⟨shape, bounded⟩
          cases shape with
          | none => simp
          | some widths =>
            rcases widths with ⟨x,y,z,out⟩
            simp only [bind_ok]
            step*
        | none =>
          simp only [bind_ok]
          step*
end Itasca.Compiler

end

/-! ## Well Formed Total -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Jump-table validation terminates for arbitrary stored entries. -/
@[step] theorem check_jump_tables_total
    (entries : alloc.vec.Vec U32) (length : Usize) (valid : Bool) (index : Usize) :
    runtime.bytecode.CompiledFunction.well_formed_loop1 entries length valid index ⦃ _ => True ⦄ := by
  unfold runtime.bytecode.CompiledFunction.well_formed_loop1
  apply loop.spec_decr_nat (fun state => entries.val.length - state.2.val) (fun _ => True)
  · rintro ⟨valid, index⟩ _
    unfold runtime.bytecode.CompiledFunction.well_formed_loop1.body
    dsimp only
    split
    · cases valid with
      | false => simp
      | true =>
        simp only [↓reduceIte]
        step as ⟨entry, found⟩
        step as ⟨target, targetEq⟩
        split <;> step* <;> scalar_tac
    · simp
  · trivial

/-- Control-map validation terminates even when a stored range is invalid. -/
@[step] theorem check_control_maps_total
    (entries : alloc.vec.Vec runtime.compiler.ControlMap) (first last length : Usize)
    (valid : Bool) (index : Usize) :
    runtime.bytecode.CompiledFunction.well_formed_loop2 entries first last length valid index ⦃ _ => True ⦄ := by
  unfold runtime.bytecode.CompiledFunction.well_formed_loop2
  apply loop.spec_decr_nat (fun state => entries.val.length - state.2.val) (fun _ => True)
  · rintro ⟨valid, index⟩ _
    unfold runtime.bytecode.CompiledFunction.well_formed_loop2.body
    dsimp only
    split
    · cases valid with
      | false => simp
      | true =>
        simp only [↓reduceIte]
        step as ⟨entry, found⟩
        repeat' first | split | step | simp only [bind_ok, WP.spec_ok]
        all_goals scalar_tac
    · simp
  · trivial

/-- Instruction validation walks a bounded code vector; source coordinates are
only read when the function has a matching source-offset vector. -/
@[step] theorem check_instructions_total (f : runtime.bytecode.CompiledFunction)
    (length : Usize) (synthetic valid : Bool) (index : Usize)
    (codeLength : length.val = f.code.val.length)
    (sourceLength : synthetic = false → f.source_offsets.val.length = f.code.val.length) :
    checkInstructions f length synthetic valid index ⦃ _ => True ⦄ := by
  unfold checkInstructions runtime.bytecode.CompiledFunction.well_formed_loop0
  apply loop.spec_decr_nat (fun state => length.val - state.2.val) (fun _ => True)
  · rintro ⟨valid, index⟩ _
    unfold runtime.bytecode.CompiledFunction.well_formed_loop0.body
    dsimp only
    split
    · cases valid with
      | false => simp
      | true =>
        simp only [↓reduceIte]
        have sourceBound : synthetic = false → index.val < f.source_offsets.val.length := by
          intro isSource
          rw [sourceLength isSource]
          scalar_tac
        cases synthetic with
        | true =>
          simp only [↓reduceIte, bind_ok]
          step as ⟨instruction, found⟩
          step with instruction_valid_total f instruction as ⟨checked, _⟩
          split <;> step* <;> scalar_tac
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          have bounded := sourceBound rfl
          step as ⟨source, found⟩
          repeat' first | split | step | simp only [bind_ok, WP.spec_ok]
          all_goals first | step with instruction_valid_total f _ | skip
          all_goals repeat' first | split | step
          all_goals scalar_tac
    · simp
  · trivial

@[step] theorem is_return_total (instruction : runtime.bytecode.Instr) :
    runtime.bytecode.is_return instruction ⦃ _ => True ⦄ := by
  cases instruction <;> simp [runtime.bytecode.is_return]

/-- All three checker passes return normally, independently of whether they
accept the function. -/
theorem checked_tail_total (f : runtime.bytecode.CompiledFunction) (length : Usize)
    (synthetic : Bool) (codeLength : length.val = f.code.val.length)
    (sourceLength : synthetic = false → f.source_offsets.val.length = f.code.val.length) :
    (do
      let valid ← checkInstructions f length synthetic true 0#usize
      let valid' ← runtime.bytecode.CompiledFunction.well_formed_loop1 f.jump_tables length valid 0#usize
      runtime.bytecode.CompiledFunction.well_formed_loop2 f.controls f.body_start f.body_end length valid' 0#usize)
      ⦃ _ => True ⦄ := by
  step with check_instructions_total f length synthetic true 0#usize codeLength sourceLength
  step*

/-- The actual bytecode publication gate terminates on arbitrary compiled
records, including invalid instructions, metadata, and coordinates. -/
theorem well_formed_total (f : runtime.bytecode.CompiledFunction) :
    runtime.bytecode.CompiledFunction.well_formed f ⦃ _ => True ⦄ := by
  unfold runtime.bytecode.CompiledFunction.well_formed
  simp only [alloc.vec.Vec.is_empty, bind_ok]
  repeat' first
    | contradiction
    | apply checked_tail_total f (alloc.vec.Vec.len f.code) _ rfl <;> (intro h; scalar_tac)
    | (split <;> try simp only [bind_ok, WP.spec_ok])
    | step
    | scalar_tac
end Itasca.Compiler

end

end

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- The synthetic instruction pass accepts when every remaining actual
instruction passes its independent slot/index checks. -/
theorem check_synthetic_instructions_accepts (function : runtime.bytecode.CompiledFunction)
    (length index : Usize) (codeLength : length.val = function.code.length)
    (inside : index.val ≤ length.val)
    (valid : ∀ (j : Nat) (bound : j < function.code.length),
      runtime.bytecode.CompiledFunction.instruction_valid function function.code.val[j] = .ok true) :
    checkInstructions function length true true index ⦃ result => result = true ⦄ := by
  unfold checkInstructions runtime.bytecode.CompiledFunction.well_formed_loop0
  apply loop.spec_decr_nat (fun state => length.val - state.2.val)
    (fun state => state.1 = true ∧ state.2.val ≤ length.val)
  · rintro ⟨flag,current⟩ ⟨rfl,bounded⟩
    unfold runtime.bytecode.CompiledFunction.well_formed_loop0.body
    dsimp only
    split
    · rename_i more
      have atCode : current.val < function.code.length := by scalar_tac
      simp only [↓reduceIte,bind_ok]
      step as ⟨instruction,found⟩
      rw [found,valid current.val atCode]
      simp only [↓reduceIte,bind_ok]
      step as ⟨next,advanced⟩
      all_goals scalar_tac
    · simp
  · exact ⟨rfl,inside⟩

/-- Jump-table checking accepts when each stored target is within the code
vector. This premise is a numeric bound, not an assumed checker result. -/
theorem check_jump_tables_accepts (entries : alloc.vec.Vec U32) (length index : Usize)
    (inside : index.val ≤ entries.length)
    (targets : ∀ entry ∈ entries.val, entry.val < length.val) :
    runtime.bytecode.CompiledFunction.well_formed_loop1 entries length true index ⦃ result => result = true ⦄ := by
  unfold runtime.bytecode.CompiledFunction.well_formed_loop1
  apply loop.spec_decr_nat (fun state => entries.length - state.2.val)
    (fun state => state.1 = true ∧ state.2.val ≤ entries.length)
  · rintro ⟨flag,current⟩ ⟨rfl,bounded⟩
    unfold runtime.bytecode.CompiledFunction.well_formed_loop1.body
    dsimp only
    split
    · rename_i more
      have atCode : current.val < entries.length := by scalar_tac
      simp only [↓reduceIte]
      step as ⟨entry,found⟩
      have target := targets entry (by rw [found]; exact List.getElem_mem atCode)
      step as ⟨word,wordEq⟩
      have below : ¬ word ≥ length := by scalar_tac
      simp only [if_neg below,bind_ok]
      step as ⟨next,advanced⟩
      all_goals scalar_tac
    · simp
  · exact ⟨rfl,inside⟩

/-- Control-map checking accepts independently bounded PC and source ranges. -/
theorem check_control_maps_accepts (entries : alloc.vec.Vec runtime.compiler.ControlMap)
    (first last length index : Usize) (inside : index.val ≤ entries.length)
    (ranges : ∀ entry ∈ entries.val,
      entry.start_pc.val ≤ entry.end_pc.val ∧ entry.end_pc.val < length.val ∧
      first.val ≤ entry.source_start.val ∧ entry.source_end.val ≤ last.val ∧
      entry.source_start.val < entry.source_end.val) :
    runtime.bytecode.CompiledFunction.well_formed_loop2 entries first last length true index
      ⦃ result => result = true ⦄ := by
  unfold runtime.bytecode.CompiledFunction.well_formed_loop2
  apply loop.spec_decr_nat (fun state => entries.length - state.2.val)
    (fun state => state.1 = true ∧ state.2.val ≤ entries.length)
  · rintro ⟨flag,current⟩ ⟨rfl,bounded⟩
    unfold runtime.bytecode.CompiledFunction.well_formed_loop2.body
    dsimp only
    split
    · rename_i more
      have atCode : current.val < entries.length := by scalar_tac
      simp only [↓reduceIte]
      step as ⟨entry,found⟩
      obtain ⟨pcOrder,pcBound,sourceStart,sourceEnd,nonempty⟩ :=
        ranges entry (by rw [found]; exact List.getElem_mem atCode)
      have hpcOrder : ¬ entry.start_pc > entry.end_pc := by scalar_tac
      have hpcBound : ¬ entry.end_pc ≥ length := by scalar_tac
      have hsourceStart : ¬ entry.source_start < first := by scalar_tac
      have hsourceEnd : ¬ entry.source_end > last := by scalar_tac
      have hnonempty : ¬ entry.source_start ≥ entry.source_end := by scalar_tac
      simp only [if_neg hpcOrder,if_neg hpcBound,if_neg hsourceStart,if_neg hsourceEnd,if_neg hnonempty,bind_ok]
      step as ⟨next,advanced⟩
      all_goals scalar_tac
    · simp
  · exact ⟨rfl,inside⟩

/-- A synthetic function passes the publication gate from its exact source
shape and local slot/index checks. No whole-checker acceptance is a premise. -/
theorem well_formed_synthetic_accepts (function : runtime.bytecode.CompiledFunction)
    (start : function.body_start = 0#usize) (finish : function.body_end = 0#usize)
    (nonempty : 0 < function.code.length) (offsets : function.source_offsets.val = [])
    (locals : function.local_slots.val ≤ function.slot_count.val)
    (params : function.param_slots.val ≤ function.local_slots.val)
    (returnStart returnCount : U32)
    (last : function.code.val[function.code.length-1]? = some (.Return returnStart returnCount))
    (instructions : ∀ (j : Nat) (bound : j < function.code.length),
      runtime.bytecode.CompiledFunction.instruction_valid function function.code.val[j] = .ok true)
    (targets : ∀ entry ∈ function.jump_tables.val, entry.val < function.code.length)
    (ranges : ∀ entry ∈ function.controls.val,
      entry.start_pc.val ≤ entry.end_pc.val ∧ entry.end_pc.val < function.code.length ∧
      entry.source_start.val = 0 ∧ entry.source_end.val = 0 ∧ entry.source_start.val < entry.source_end.val) :
    runtime.bytecode.CompiledFunction.well_formed function ⦃ result => result = true ⦄ := by
  have sourceEmpty : function.source_offsets = alloc.vec.Vec.new _ := alloc.vec.Vec.ext _ _ offsets
  have notEmpty : alloc.vec.Vec.len function.code ≠ 0#usize := by scalar_tac
  have notLocals : ¬ function.local_slots > function.slot_count := by scalar_tac
  have notParams : ¬ function.param_slots > function.local_slots := by scalar_tac
  unfold runtime.bytecode.CompiledFunction.well_formed
  simp [start,finish,sourceEmpty,alloc.vec.Vec.is_empty,notEmpty,notLocals,notParams]
  step as ⟨index,indexEq⟩
  have indexValue : index.val = function.code.length - 1 := by scalar_tac
  have atCode : index.val < function.code.length := by omega
  step as ⟨instruction,found⟩
  have selected : instruction = .Return returnStart returnCount := by
    have atLast : function.code.val[index.val]? = some instruction := by
      simp [List.getElem?_eq_getElem atCode, found]
    rw [indexValue, last] at atLast
    exact (Option.some.inj atLast).symm
  rw [selected]
  simp only [runtime.bytecode.is_return,bind_ok,↓reduceIte]
  have instructionPass := check_synthetic_instructions_accepts function (alloc.vec.Vec.len function.code)
    0#usize rfl (by scalar_tac) instructions
  simp only [checkInstructions,start,finish,sourceEmpty] at instructionPass
  step with instructionPass as ⟨checked,accepted⟩
  rw [accepted]
  step with check_jump_tables_accepts function.jump_tables (alloc.vec.Vec.len function.code) 0#usize
    (by scalar_tac) targets as ⟨checked,accepted⟩
  rw [accepted]
  apply check_control_maps_accepts function.controls 0#usize 0#usize
    (alloc.vec.Vec.len function.code) 0#usize (by scalar_tac)
  intro entry member
  obtain ⟨order,bound,first,last,positive⟩ := ranges entry member
  exact ⟨order,bound,by scalar_tac,by scalar_tac,positive⟩

end Itasca.Compiler

end
