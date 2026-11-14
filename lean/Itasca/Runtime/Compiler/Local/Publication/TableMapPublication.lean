import Itasca.Runtime.Compiler.Local.Coordinates.ScalarSourceCoordinates
import Itasca.Runtime.Compiler.Local.Publication.ScopeEntryPublication
import Itasca.Runtime.Compiler.Local.Callbacks.CodeGrowth.CompilerCodeMonotoneLiteral
import Itasca.Runtime.Compiler.Local.Publication.StartMapPublication
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableSafetyEffects

/-!
Sections, each formerly its own module: ScalarMapPublication, TableMapPublication.
-/

/-! ## ScalarMapPublication -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

private def ScalarMapRule {A : Type} (ops : runtime.platform.Alloc A) (opcode : U16) : Prop :=
  ∀ (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) (a b : U32) (bits : U128),
    ControlMapPublication before → before.next_source.val ≤ state.pos.val →
    runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after) →
    ControlMapPublication after

private theorem scalar_maps_0 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarMapRule ops 0#u16 := by
  intro before after state a b bits held forward called
  by_cases live : before.reachable = true
  · have stable : CompilerOrdinaryStable before after := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | metadata_step called using ops, law
    have growth : before.function.code.val.length ≤ after.function.code.val.length := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
    have cursor : after.next_source = state.pos := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | cursor_step called using ops, law
    apply held.ordinary stable growth
    rw [cursor]
    exact forward
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact compiler_observe_map_publication ops law before after state held forward called

private theorem scalar_maps_1 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarMapRule ops 1#u16 := by
  intro before after state a b bits held forward called
  by_cases live : before.reachable = true
  · have stable : CompilerOrdinaryStable before after := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | metadata_step called using ops, law
    have growth : before.function.code.val.length ≤ after.function.code.val.length := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
    have cursor : after.next_source = state.pos := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | cursor_step called using ops, law
    apply held.ordinary stable growth
    rw [cursor]
    exact forward
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact compiler_observe_map_publication ops law before after state held forward called

private theorem scalar_maps_16 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarMapRule ops 16#u16 := by
  intro before after state a b bits held forward called
  by_cases live : before.reachable = true
  · have stable : CompilerOrdinaryStable before after := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | metadata_step called using ops, law
    have growth : before.function.code.val.length ≤ after.function.code.val.length := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
    have cursor : after.next_source = state.pos := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | cursor_step called using ops, law
    apply held.ordinary stable growth
    rw [cursor]
    exact forward
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact compiler_observe_map_publication ops law before after state held forward called

private theorem scalar_maps_17 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarMapRule ops 17#u16 := by
  intro before after state a b bits held forward called
  by_cases live : before.reachable = true
  · have stable : CompilerOrdinaryStable before after := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | metadata_step called using ops, law
    have growth : before.function.code.val.length ≤ after.function.code.val.length := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
    have cursor : after.next_source = state.pos := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | cursor_step called using ops, law
    apply held.ordinary stable growth
    rw [cursor]
    exact forward
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact compiler_observe_map_publication ops law before after state held forward called

private theorem scalar_maps_26 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarMapRule ops 26#u16 := by
  intro before after state a b bits held forward called
  by_cases live : before.reachable = true
  · have stable : CompilerOrdinaryStable before after := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | metadata_step called using ops, law
    have growth : before.function.code.val.length ≤ after.function.code.val.length := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
    have cursor : after.next_source = state.pos := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | cursor_step called using ops, law
    apply held.ordinary stable growth
    rw [cursor]
    exact forward
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact compiler_observe_map_publication ops law before after state held forward called

private theorem scalar_maps_27 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarMapRule ops 27#u16 := by
  intro before after state a b bits held forward called
  by_cases live : before.reachable = true
  · have stable : CompilerOrdinaryStable before after := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | metadata_step called using ops, law
    have growth : before.function.code.val.length ≤ after.function.code.val.length := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
    have cursor : after.next_source = state.pos := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | cursor_step called using ops, law
    apply held.ordinary stable growth
    rw [cursor]
    exact forward
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact compiler_observe_map_publication ops law before after state held forward called

private theorem scalar_maps_28 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarMapRule ops 28#u16 := by
  intro before after state a b bits held forward called
  by_cases live : before.reachable = true
  · have stable : CompilerOrdinaryStable before after := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | metadata_step called using ops, law
    have growth : before.function.code.val.length ≤ after.function.code.val.length := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
    have cursor : after.next_source = state.pos := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | cursor_step called using ops, law
    apply held.ordinary stable growth
    rw [cursor]
    exact forward
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact compiler_observe_map_publication ops law before after state held forward called

private theorem scalar_maps_32 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarMapRule ops 32#u16 := by
  intro before after state a b bits held forward called
  by_cases live : before.reachable = true
  · have stable : CompilerOrdinaryStable before after := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | metadata_step called using ops, law
    have growth : before.function.code.val.length ≤ after.function.code.val.length := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
    have cursor : after.next_source = state.pos := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | cursor_step called using ops, law
    apply held.ordinary stable growth
    rw [cursor]
    exact forward
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact compiler_observe_map_publication ops law before after state held forward called

private theorem scalar_maps_33 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarMapRule ops 33#u16 := by
  intro before after state a b bits held forward called
  by_cases live : before.reachable = true
  · have stable : CompilerOrdinaryStable before after := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | metadata_step called using ops, law
    have growth : before.function.code.val.length ≤ after.function.code.val.length := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
    have cursor : after.next_source = state.pos := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | cursor_step called using ops, law
    apply held.ordinary stable growth
    rw [cursor]
    exact forward
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact compiler_observe_map_publication ops law before after state held forward called

private theorem scalar_maps_34 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarMapRule ops 34#u16 := by
  intro before after state a b bits held forward called
  by_cases live : before.reachable = true
  · have stable : CompilerOrdinaryStable before after := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | metadata_step called using ops, law
    have growth : before.function.code.val.length ≤ after.function.code.val.length := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
    have cursor : after.next_source = state.pos := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | cursor_step called using ops, law
    apply held.ordinary stable growth
    rw [cursor]
    exact forward
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact compiler_observe_map_publication ops law before after state held forward called

private theorem scalar_maps_35 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarMapRule ops 35#u16 := by
  intro before after state a b bits held forward called
  by_cases live : before.reachable = true
  · have stable : CompilerOrdinaryStable before after := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | metadata_step called using ops, law
    have growth : before.function.code.val.length ≤ after.function.code.val.length := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
    have cursor : after.next_source = state.pos := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | cursor_step called using ops, law
    apply held.ordinary stable growth
    rw [cursor]
    exact forward
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact compiler_observe_map_publication ops law before after state held forward called

private theorem scalar_maps_36 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarMapRule ops 36#u16 := by
  intro before after state a b bits held forward called
  by_cases live : before.reachable = true
  · have stable : CompilerOrdinaryStable before after := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | metadata_step called using ops, law
    have growth : before.function.code.val.length ≤ after.function.code.val.length := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
    have cursor : after.next_source = state.pos := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | cursor_step called using ops, law
    apply held.ordinary stable growth
    rw [cursor]
    exact forward
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact compiler_observe_map_publication ops law before after state held forward called

private theorem scalar_maps_37 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarMapRule ops 37#u16 := by
  intro before after state a b bits held forward called
  by_cases live : before.reachable = true
  · have stable : CompilerOrdinaryStable before after := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | metadata_step called using ops, law
    have growth : before.function.code.val.length ≤ after.function.code.val.length := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
    have cursor : after.next_source = state.pos := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | cursor_step called using ops, law
    apply held.ordinary stable growth
    rw [cursor]
    exact forward
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact compiler_observe_map_publication ops law before after state held forward called

private theorem scalar_maps_38 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarMapRule ops 38#u16 := by
  intro before after state a b bits held forward called
  by_cases live : before.reachable = true
  · have stable : CompilerOrdinaryStable before after := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | metadata_step called using ops, law
    have growth : before.function.code.val.length ≤ after.function.code.val.length := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
    have cursor : after.next_source = state.pos := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | cursor_step called using ops, law
    apply held.ordinary stable growth
    rw [cursor]
    exact forward
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact compiler_observe_map_publication ops law before after state held forward called

private theorem scalar_maps_63 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarMapRule ops 63#u16 := by
  intro before after state a b bits held forward called
  by_cases live : before.reachable = true
  · have stable : CompilerOrdinaryStable before after := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | metadata_step called using ops, law
    have growth : before.function.code.val.length ≤ after.function.code.val.length := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
    have cursor : after.next_source = state.pos := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | cursor_step called using ops, law
    apply held.ordinary stable growth
    rw [cursor]
    exact forward
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact compiler_observe_map_publication ops law before after state held forward called

private theorem scalar_maps_64 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarMapRule ops 64#u16 := by
  intro before after state a b bits held forward called
  by_cases live : before.reachable = true
  · have stable : CompilerOrdinaryStable before after := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | metadata_step called using ops, law
    have growth : before.function.code.val.length ≤ after.function.code.val.length := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
    have cursor : after.next_source = state.pos := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | cursor_step called using ops, law
    apply held.ordinary stable growth
    rw [cursor]
    exact forward
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact compiler_observe_map_publication ops law before after state held forward called

private theorem scalar_maps_65 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarMapRule ops 65#u16 := by
  intro before after state a b bits held forward called
  by_cases live : before.reachable = true
  · have stable : CompilerOrdinaryStable before after := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | metadata_step called using ops, law
    have growth : before.function.code.val.length ≤ after.function.code.val.length := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
    have cursor : after.next_source = state.pos := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | cursor_step called using ops, law
    apply held.ordinary stable growth
    rw [cursor]
    exact forward
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact compiler_observe_map_publication ops law before after state held forward called

private theorem scalar_maps_66 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarMapRule ops 66#u16 := by
  intro before after state a b bits held forward called
  by_cases live : before.reachable = true
  · have stable : CompilerOrdinaryStable before after := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | metadata_step called using ops, law
    have growth : before.function.code.val.length ≤ after.function.code.val.length := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
    have cursor : after.next_source = state.pos := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | cursor_step called using ops, law
    apply held.ordinary stable growth
    rw [cursor]
    exact forward
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact compiler_observe_map_publication ops law before after state held forward called

private theorem scalar_maps_67 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarMapRule ops 67#u16 := by
  intro before after state a b bits held forward called
  by_cases live : before.reachable = true
  · have stable : CompilerOrdinaryStable before after := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | metadata_step called using ops, law
    have growth : before.function.code.val.length ≤ after.function.code.val.length := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
    have cursor : after.next_source = state.pos := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | cursor_step called using ops, law
    apply held.ordinary stable growth
    rw [cursor]
    exact forward
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact compiler_observe_map_publication ops law before after state held forward called

private theorem scalar_maps_68 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarMapRule ops 68#u16 := by
  intro before after state a b bits held forward called
  by_cases live : before.reachable = true
  · have stable : CompilerOrdinaryStable before after := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | metadata_step called using ops, law
    have growth : before.function.code.val.length ≤ after.function.code.val.length := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
    have cursor : after.next_source = state.pos := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | cursor_step called using ops, law
    apply held.ordinary stable growth
    rw [cursor]
    exact forward
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact compiler_observe_map_publication ops law before after state held forward called

private theorem scalar_maps_208 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarMapRule ops 208#u16 := by
  intro before after state a b bits held forward called
  by_cases live : before.reachable = true
  · have stable : CompilerOrdinaryStable before after := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | metadata_step called using ops, law
    have growth : before.function.code.val.length ≤ after.function.code.val.length := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
    have cursor : after.next_source = state.pos := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | cursor_step called using ops, law
    apply held.ordinary stable growth
    rw [cursor]
    exact forward
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact compiler_observe_map_publication ops law before after state held forward called

private theorem scalar_maps_209 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarMapRule ops 209#u16 := by
  intro before after state a b bits held forward called
  by_cases live : before.reachable = true
  · have stable : CompilerOrdinaryStable before after := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | metadata_step called using ops, law
    have growth : before.function.code.val.length ≤ after.function.code.val.length := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
    have cursor : after.next_source = state.pos := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | cursor_step called using ops, law
    apply held.ordinary stable growth
    rw [cursor]
    exact forward
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact compiler_observe_map_publication ops law before after state held forward called

private theorem scalar_maps_210 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarMapRule ops 210#u16 := by
  intro before after state a b bits held forward called
  by_cases live : before.reachable = true
  · have stable : CompilerOrdinaryStable before after := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | metadata_step called using ops, law
    have growth : before.function.code.val.length ≤ after.function.code.val.length := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
    have cursor : after.next_source = state.pos := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | cursor_step called using ops, law
    apply held.ordinary stable growth
    rw [cursor]
    exact forward
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact compiler_observe_map_publication ops law before after state held forward called

private theorem scalar_maps_264 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarMapRule ops 264#u16 := by
  intro before after state a b bits held forward called
  by_cases live : before.reachable = true
  · have stable : CompilerOrdinaryStable before after := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | metadata_step called using ops, law
    have growth : before.function.code.val.length ≤ after.function.code.val.length := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
    have cursor : after.next_source = state.pos := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | cursor_step called using ops, law
    apply held.ordinary stable growth
    rw [cursor]
    exact forward
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact compiler_observe_map_publication ops law before after state held forward called

private theorem scalar_maps_265 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarMapRule ops 265#u16 := by
  intro before after state a b bits held forward called
  by_cases live : before.reachable = true
  · have stable : CompilerOrdinaryStable before after := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | metadata_step called using ops, law
    have growth : before.function.code.val.length ≤ after.function.code.val.length := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
    have cursor : after.next_source = state.pos := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | cursor_step called using ops, law
    apply held.ordinary stable growth
    rw [cursor]
    exact forward
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact compiler_observe_map_publication ops law before after state held forward called

private theorem scalar_maps_266 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarMapRule ops 266#u16 := by
  intro before after state a b bits held forward called
  by_cases live : before.reachable = true
  · have stable : CompilerOrdinaryStable before after := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | metadata_step called using ops, law
    have growth : before.function.code.val.length ≤ after.function.code.val.length := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
    have cursor : after.next_source = state.pos := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | cursor_step called using ops, law
    apply held.ordinary stable growth
    rw [cursor]
    exact forward
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact compiler_observe_map_publication ops law before after state held forward called

private theorem scalar_maps_267 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarMapRule ops 267#u16 := by
  intro before after state a b bits held forward called
  by_cases live : before.reachable = true
  · have stable : CompilerOrdinaryStable before after := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | metadata_step called using ops, law
    have growth : before.function.code.val.length ≤ after.function.code.val.length := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
    have cursor : after.next_source = state.pos := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | cursor_step called using ops, law
    apply held.ordinary stable growth
    rw [cursor]
    exact forward
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact compiler_observe_map_publication ops law before after state held forward called

private theorem scalar_maps_268 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarMapRule ops 268#u16 := by
  intro before after state a b bits held forward called
  by_cases live : before.reachable = true
  · have stable : CompilerOrdinaryStable before after := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | metadata_step called using ops, law
    have growth : before.function.code.val.length ≤ after.function.code.val.length := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
    have cursor : after.next_source = state.pos := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | cursor_step called using ops, law
    apply held.ordinary stable growth
    rw [cursor]
    exact forward
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact compiler_observe_map_publication ops law before after state held forward called

private theorem scalar_maps_269 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarMapRule ops 269#u16 := by
  intro before after state a b bits held forward called
  by_cases live : before.reachable = true
  · have stable : CompilerOrdinaryStable before after := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | metadata_step called using ops, law
    have growth : before.function.code.val.length ≤ after.function.code.val.length := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
    have cursor : after.next_source = state.pos := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | cursor_step called using ops, law
    apply held.ordinary stable growth
    rw [cursor]
    exact forward
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact compiler_observe_map_publication ops law before after state held forward called

private theorem scalar_maps_270 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarMapRule ops 270#u16 := by
  intro before after state a b bits held forward called
  by_cases live : before.reachable = true
  · have stable : CompilerOrdinaryStable before after := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | metadata_step called using ops, law
    have growth : before.function.code.val.length ≤ after.function.code.val.length := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
    have cursor : after.next_source = state.pos := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | cursor_step called using ops, law
    apply held.ordinary stable growth
    rw [cursor]
    exact forward
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact compiler_observe_map_publication ops law before after state held forward called

private theorem scalar_maps_271 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarMapRule ops 271#u16 := by
  intro before after state a b bits held forward called
  by_cases live : before.reachable = true
  · have stable : CompilerOrdinaryStable before after := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | metadata_step called using ops, law
    have growth : before.function.code.val.length ≤ after.function.code.val.length := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
    have cursor : after.next_source = state.pos := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | cursor_step called using ops, law
    apply held.ordinary stable growth
    rw [cursor]
    exact forward
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact compiler_observe_map_publication ops law before after state held forward called

private theorem scalar_maps_272 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarMapRule ops 272#u16 := by
  intro before after state a b bits held forward called
  by_cases live : before.reachable = true
  · have stable : CompilerOrdinaryStable before after := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | metadata_step called using ops, law
    have growth : before.function.code.val.length ≤ after.function.code.val.length := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
    have cursor : after.next_source = state.pos := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | cursor_step called using ops, law
    apply held.ordinary stable growth
    rw [cursor]
    exact forward
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact compiler_observe_map_publication ops law before after state held forward called

private theorem scalar_maps_273 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ScalarMapRule ops 273#u16 := by
  intro before after state a b bits held forward called
  by_cases live : before.reachable = true
  · have stable : CompilerOrdinaryStable before after := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | metadata_step called using ops, law
    have growth : before.function.code.val.length ≤ after.function.code.val.length := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | code_mono_step called using ops, law
    have cursor : after.next_source = state.pos := by
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | cursor_step called using ops, law
    apply held.ordinary stable growth
    rw [cursor]
    exact forward
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)] at called
    exact compiler_observe_map_publication ops law before after state held forward called

/-- Every finite nonnumeric ordinary opcode preserves control-map bounds,
including all immediate bits and unreachable code. -/
theorem compiler_scalar_op_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (supported : opcode ∈ sourceCoordinateScalarOpcodes)
    (held : ControlMapPublication before) (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after)) :
    ControlMapPublication after := by
  simp only [sourceCoordinateScalarOpcodes,List.mem_cons,List.not_mem_nil,or_false] at supported
  rcases supported with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact scalar_maps_0 ops law before after state a b bits held forward called
  · exact scalar_maps_1 ops law before after state a b bits held forward called
  · exact scalar_maps_16 ops law before after state a b bits held forward called
  · exact scalar_maps_17 ops law before after state a b bits held forward called
  · exact scalar_maps_26 ops law before after state a b bits held forward called
  · exact scalar_maps_27 ops law before after state a b bits held forward called
  · exact scalar_maps_28 ops law before after state a b bits held forward called
  · exact scalar_maps_32 ops law before after state a b bits held forward called
  · exact scalar_maps_33 ops law before after state a b bits held forward called
  · exact scalar_maps_34 ops law before after state a b bits held forward called
  · exact scalar_maps_35 ops law before after state a b bits held forward called
  · exact scalar_maps_36 ops law before after state a b bits held forward called
  · exact scalar_maps_37 ops law before after state a b bits held forward called
  · exact scalar_maps_38 ops law before after state a b bits held forward called
  · exact scalar_maps_63 ops law before after state a b bits held forward called
  · exact scalar_maps_64 ops law before after state a b bits held forward called
  · exact scalar_maps_65 ops law before after state a b bits held forward called
  · exact scalar_maps_66 ops law before after state a b bits held forward called
  · exact scalar_maps_67 ops law before after state a b bits held forward called
  · exact scalar_maps_68 ops law before after state a b bits held forward called
  · exact scalar_maps_208 ops law before after state a b bits held forward called
  · exact scalar_maps_209 ops law before after state a b bits held forward called
  · exact scalar_maps_210 ops law before after state a b bits held forward called
  · exact scalar_maps_264 ops law before after state a b bits held forward called
  · exact scalar_maps_265 ops law before after state a b bits held forward called
  · exact scalar_maps_266 ops law before after state a b bits held forward called
  · exact scalar_maps_267 ops law before after state a b bits held forward called
  · exact scalar_maps_268 ops law before after state a b bits held forward called
  · exact scalar_maps_269 ops law before after state a b bits held forward called
  · exact scalar_maps_270 ops law before after state a b bits held forward called
  · exact scalar_maps_271 ops law before after state a b bits held forward called
  · exact scalar_maps_272 ops law before after state a b bits held forward called
  · exact scalar_maps_273 ops law before after state a b bits held forward called

end Itasca.Runtime.Compiler

end

/-! ## TableMapPublication -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- Emitted code extends the target range without changing map owners or source bounds. -/
theorem Emitted.control_maps {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {instruction : runtime.bytecode.Instr} (emitted : Emitted before after instruction)
    (held : ControlMapPublication before) : ControlMapPublication after := by
  have stable := emitted.ordinary_stable
  obtain ⟨budget,code,sources,rfl,codeAppend,_⟩ := emitted
  apply held.ordinary stable
  · change before.function.code.val.length ≤ code.val.length
    rw [codeAppend]
    simp
  · exact le_rfl

/-- Streamed labels retain all map bounds, including Wasm 1 label collection. -/
theorem compiler_table_label_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (held : ControlMapPublication before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label
      ops before state depth = .ok (.Ok (),after)) : ControlMapPublication after := by
  obtain ⟨budget,depths,frame,_⟩ := compiler_table_label_success ops law before after state depth called
  rw [frame]
  exact held.retained ⟨rfl,le_rfl⟩ rfl rfl le_rfl le_rfl

/-- Each actual table stub preserves map publication bounds. -/
theorem compiler_table_branch_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (depth : U32) (lookup : before.table_depths.val[index.val]? = some depth)
    (held : ControlMapPublication before)
    (called : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (.Ok (),after)) :
    ControlMapPublication after := by
  obtain ⟨target,budget,table,_,_,branch⟩ := compiler_table_branch_success ops law before after index depth lookup called
  let staged := {before with budget,function := {before.function with jump_tables := table}}
  change runtime.compiler.control.FunctionCompiler.branch ops staged depth 1#u32 false = .ok (.Ok (),after) at branch
  exact compiler_branch_map_publication ops law staged after depth 1#u32 false
    (held.retained ⟨rfl,le_rfl⟩ rfl rfl le_rfl le_rfl) branch

/-- Every branch in a finite table-lowering run retains map bounds. -/
theorem TableBranchRun.control_maps {A : Type} {ops : runtime.platform.Alloc A}
    (law : Platform.AllocCorrect ops) {before after : runtime.compiler.FunctionCompiler A}
    {index : Nat} (run : TableBranchRun ops before index after) :
    ControlMapPublication before →
    ControlMapPublication after ∧ after.next_source = before.next_source := by
  induction run with
  | done => intro held; exact ⟨held,rfl⟩
  | @cons before middle after index inbounds called rest ih =>
    intro held
    let depth := before.table_depths.val[index.val]
    have lookup : before.table_depths.val[index.val]? = some depth := List.getElem?_eq_getElem inbounds
    have coordinates := compiler_table_branch_map_publication ops law before middle index depth lookup held called
    have cursor := compiler_table_branch_cursor ops law before middle index depth lookup called
    obtain ⟨final,finalCursor⟩ := ih coordinates
    exact ⟨final,finalCursor.trans cursor⟩

/-- Dispatch and every target stub preserve map bounds in the actual lowerer. -/
theorem compiler_lower_table_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (held : ControlMapPublication before)
    (called : runtime.compiler.control.FunctionCompiler.lower_table_branches ops before = .ok (.Ok (),after)) :
    ControlMapPublication after ∧ after.next_source = before.next_source := by
  obtain ⟨start,len,selector,emitted,_,_,_,emission,run⟩ := compiler_lower_table_success ops law before after called
  have coordinates := emission.control_maps held
  obtain ⟨budget,code,sources,frame,_,_⟩ := emission
  obtain ⟨final,cursor⟩ := run.control_maps law coordinates
  exact ⟨final,by simpa only [frame] using cursor⟩

/-- The actual full branch-table callback preserves all map publication bounds. -/
theorem compiler_br_table_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (fallback : U32) (types : Itasca.signature.ResultType)
    (held : ControlMapPublication before)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state fallback types = .ok (.Ok (),after)) : ControlMapPublication after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table at called
  obtain ⟨⟨result,labeled⟩,labelCalled,rest⟩ := bind_ok_inv _ _ _ called
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok unit =>
    cases unit
    obtain ⟨budget,depths,frame,_⟩ := compiler_table_label_success ops law before labeled state fallback labelCalled
    have coordinates : ControlMapPublication labeled := by
      rw [frame]
      exact held.retained ⟨rfl,le_rfl⟩ rfl rfl le_rfl le_rfl
    have cursor : labeled.next_source = before.next_source := by rw [frame]
    simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
    split at rest
    · obtain ⟨⟨result,lowered⟩,lowerCalled,rest⟩ := bind_ok_inv _ _ _ rest
      cases result with
      | Err error =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
      | Ok unit =>
        cases unit
        obtain ⟨loweredCoordinates,loweredCursor⟩ :=
          compiler_lower_table_map_publication ops law labeled lowered coordinates lowerCalled
        simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
        obtain ⟨cleared,_,observed⟩ := bind_ok_inv _ _ _ rest
        exact compiler_observe_map_publication ops law {lowered with reachable := false,table_depths := cleared} after state
          (loweredCoordinates.retained ⟨rfl,le_rfl⟩ rfl rfl le_rfl le_rfl)
          (by simpa only [loweredCursor,cursor] using forward) observed
    · obtain ⟨cleared,_,observed⟩ := bind_ok_inv _ _ _ rest
      exact compiler_observe_map_publication ops law {labeled with table_depths := cleared} after state
        (coordinates.retained ⟨rfl,le_rfl⟩ rfl rfl le_rfl le_rfl) (by simpa only [cursor] using forward) observed

end Itasca.Runtime.Compiler

end
