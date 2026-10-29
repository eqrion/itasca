import Itasca.Runtime.Equations
import Itasca.Support.Result

/-!
Instruction-check loops and compiled-function well-formedness.

Main declarations: `checkInstructionBody` and `checkInstructions`. A direct consumer is `Compiler.Local.Relations.Instructions.SlotCheckAcceptance`.
-/

namespace Itasca.Runtime.Code
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
theorem checkInstructionBody_cont (f : runtime.bytecode.CompiledFunction)
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

theorem checkInstructionBody_done (f : runtime.bytecode.CompiledFunction)
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
theorem checkInstructions_valid (f : runtime.bytecode.CompiledFunction)
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
        have terminal := checkInstructionBody_done f length synthetic valid index checked
        refine ⟨terminal.2, ?_⟩
        intro j lower upper
        omega
      | cont state =>
        rcases state with ⟨nextValid, nextIndex⟩
        have advanced := checkInstructionBody_cont f length synthetic valid nextValid index nextIndex lengthEq checked
        have smaller : length.val - nextIndex.val < n := by omega
        have remaining := ih _ smaller nextIndex nextValid rfl rest
        have current := advanced.2.2.2 remaining.1
        refine ⟨advanced.2.1, ?_⟩
        intro j lower upper
        by_cases same : j = index.val
        · subst j; exact current
        · exact remaining.2 j (by omega) upper
  exact main _ index valid rfl run

theorem checkJumpTable_false (values : alloc.vec.Vec U32) (length index : Usize) :
    runtime.bytecode.CompiledFunction.well_formed_loop1 values length false index = .ok false := by
  unfold runtime.bytecode.CompiledFunction.well_formed_loop1
  rw [loop.eq_def]
  simp only [runtime.bytecode.CompiledFunction.well_formed_loop1.body]
  split <;> simp

theorem checkControls_false (values : alloc.vec.Vec runtime.compiler.ControlMap)
    (start stop length index : Usize) :
    runtime.bytecode.CompiledFunction.well_formed_loop2 values start stop length false index = .ok false := by
  unfold runtime.bytecode.CompiledFunction.well_formed_loop2
  rw [loop.eq_def]
  simp only [runtime.bytecode.CompiledFunction.well_formed_loop2.body]
  split <;> simp

theorem checkJumpTable_true (values : alloc.vec.Vec U32) (length index : Usize) (valid : Bool)
    (run : runtime.bytecode.CompiledFunction.well_formed_loop1 values length valid index = .ok true) :
    valid = true := by
  cases valid with
  | false => rw [checkJumpTable_false] at run; cases Result.ok_injective run
  | true => rfl

theorem checkControls_true (values : alloc.vec.Vec runtime.compiler.ControlMap)
    (start stop length index : Usize) (valid : Bool)
    (run : runtime.bytecode.CompiledFunction.well_formed_loop2 values start stop length valid index = .ok true) :
    valid = true := by
  cases valid with
  | false => rw [checkControls_false] at run; cases Result.ok_injective run
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
  have controlTrue := checkControls_true _ _ _ _ _ _ controls
  subst valid'
  have jumpsTrue := checkJumpTable_true _ _ _ _ jumps
  subst valid
  have checked := checkInstructions_valid f length synthetic true 0#usize lengthEq instructions
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

end Itasca.Runtime.Code

