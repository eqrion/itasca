import Itasca.Runtime.Compiler.Local.Relations.Instructions.WellFormed

/-! Acceptance directions for the structural publication checker. Component
validity is a local obligation to derive from emitted code and source bounds;
no complete-module compilation success is assumed by these helper lemmas. -/
namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler
