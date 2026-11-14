import Itasca.Runtime.Equations.Bytecode
import Itasca.Generated.FunsCompiler
import Itasca.Support.Result

/-!
Sections, each formerly its own module: WellFormed, SlotCheckAcceptance, CoreInstructionAcceptance, InstructionCheckAcceptance.
-/

/-! ## WellFormed -/

section

/-!
Instruction-check loops and compiled-function well-formedness.

Main declarations: `checkInstructionBody` and `checkInstructions`. A direct consumer is `Compiler.Local.Relations.Instructions.SlotCheckAcceptance`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

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

end Itasca.Runtime.Compiler

end

/-! ## SlotCheckAcceptance -/

section

/-!
Exact arithmetic acceptance of the concrete slot-range check. The upper bound is expressed in natural coordinates, avoiding unsigned subtraction.

Main declarations: `slots_fit_accepts`. A direct consumer is `Compiler.Local.Relations.Instructions.CoreInstructionAcceptance`.
-/

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## CoreInstructionAcceptance -/

section

/-!
Numerical publication obligations for non-projected bytecode forms. Global/function indices are checked by execution against its environment; the local bytecode checker checks slots and its own function-local table indices.

Main declarations: `CoreInstructionBounds`. A direct consumer is `Compiler.Local.Relations.Instructions.LinearInstructionAcceptance`.
-/

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## InstructionCheckAcceptance -/

section

/-!
Scalar operator checking accepts the exact projection supplied by lowering when its three concrete word slots fit the function's retained capacity.

Main declarations: `scalar_instruction_accepts` and `store_instruction_accepts`. A direct consumer is `Compiler.Local.Relations.Instructions.SimdInstructionAcceptance`.
-/

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end
