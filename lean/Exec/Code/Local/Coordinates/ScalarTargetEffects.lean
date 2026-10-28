import Exec.Code.Local.Coordinates.ScalarSourceCoordinates
import Exec.Code.Local.Callbacks.Table.CompilerAuxiliaryTables
import Exec.Code.Local.Callbacks.Common.CompilerCodeMonotoneTactic

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

private def ScalarTargetEffects {A : Type} (ops : runtime.platform.Alloc A) (opcode : U16) : Prop :=
  ∀ (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) (a b : U32) (bits : U128),
    runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after) →
      after.function.jump_tables.val = before.function.jump_tables.val ∧
      before.function.code.val.length ≤ after.function.code.val.length

private theorem scalar_target_effects_0 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 0#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_1 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 1#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_16 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 16#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_17 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 17#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_26 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 26#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_27 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 27#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_28 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 28#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_32 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 32#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_33 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 33#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_34 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 34#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_35 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 35#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_36 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 36#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_37 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 37#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_38 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 38#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_63 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 63#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_64 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 64#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_65 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 65#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_66 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 66#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_67 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 67#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_68 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 68#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_208 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 208#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_209 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 209#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_210 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 210#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_264 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 264#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_265 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 265#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_266 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 266#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_267 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 267#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_268 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 268#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_269 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 269#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_270 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 270#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_271 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 271#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_272 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 272#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

private theorem scalar_target_effects_273 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarTargetEffects ops 273#u16 := by
  intro before after state a b bits called
  by_cases live : before.reachable = true
  · constructor
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | auxiliary_tables_step called using ops, law
    · unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
    exact ⟨congrArg CompilerTables.jumpTables (compiler_observe_tables ops law before after state (.Ok ()) called),
      compiler_observe_code_mono ops law before after state (.Ok ()) called⟩

/-- Nonnumeric ordinary lowering preserves the complete jump table and grows
code monotonically, independently of every immediate and source stack. -/
theorem compiler_scalar_target_effects {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (supported : opcode ∈ sourceCoordinateScalarOpcodes)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after)) :
    after.function.jump_tables.val = before.function.jump_tables.val ∧
      before.function.code.val.length ≤ after.function.code.val.length := by
  simp only [sourceCoordinateScalarOpcodes,List.mem_cons,List.not_mem_nil,or_false] at supported
  rcases supported with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact scalar_target_effects_0 ops law before after state a b bits called
  · exact scalar_target_effects_1 ops law before after state a b bits called
  · exact scalar_target_effects_16 ops law before after state a b bits called
  · exact scalar_target_effects_17 ops law before after state a b bits called
  · exact scalar_target_effects_26 ops law before after state a b bits called
  · exact scalar_target_effects_27 ops law before after state a b bits called
  · exact scalar_target_effects_28 ops law before after state a b bits called
  · exact scalar_target_effects_32 ops law before after state a b bits called
  · exact scalar_target_effects_33 ops law before after state a b bits called
  · exact scalar_target_effects_34 ops law before after state a b bits called
  · exact scalar_target_effects_35 ops law before after state a b bits called
  · exact scalar_target_effects_36 ops law before after state a b bits called
  · exact scalar_target_effects_37 ops law before after state a b bits called
  · exact scalar_target_effects_38 ops law before after state a b bits called
  · exact scalar_target_effects_63 ops law before after state a b bits called
  · exact scalar_target_effects_64 ops law before after state a b bits called
  · exact scalar_target_effects_65 ops law before after state a b bits called
  · exact scalar_target_effects_66 ops law before after state a b bits called
  · exact scalar_target_effects_67 ops law before after state a b bits called
  · exact scalar_target_effects_68 ops law before after state a b bits called
  · exact scalar_target_effects_208 ops law before after state a b bits called
  · exact scalar_target_effects_209 ops law before after state a b bits called
  · exact scalar_target_effects_210 ops law before after state a b bits called
  · exact scalar_target_effects_264 ops law before after state a b bits called
  · exact scalar_target_effects_265 ops law before after state a b bits called
  · exact scalar_target_effects_266 ops law before after state a b bits called
  · exact scalar_target_effects_267 ops law before after state a b bits called
  · exact scalar_target_effects_268 ops law before after state a b bits called
  · exact scalar_target_effects_269 ops law before after state a b bits called
  · exact scalar_target_effects_270 ops law before after state a b bits called
  · exact scalar_target_effects_271 ops law before after state a b bits called
  · exact scalar_target_effects_272 ops law before after state a b bits called
  · exact scalar_target_effects_273 ops law before after state a b bits called

end Itasca.Runtime.Code
