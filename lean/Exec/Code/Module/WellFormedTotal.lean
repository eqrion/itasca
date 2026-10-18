import Exec.Code.Local.Relations.Common.WellFormed
import Exec.Code.Module.InstructionValidityTotal
namespace Exec.Code
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
end Exec.Code
