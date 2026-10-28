import Itasca.Runtime.Code.Local.Coordinates.ScalarSourceCoordinates
import Itasca.Runtime.Code.Local.Publication.OrdinaryMapPublication
import Itasca.Runtime.Code.Local.Callbacks.Common.CompilerCodeMonotoneTactic

namespace Itasca.Runtime.Code
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
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
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
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
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
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
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
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
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
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
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
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
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
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
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
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
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
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
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
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
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
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
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
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
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
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
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
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
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
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
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
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
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
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
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
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
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
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
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
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
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
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
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
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
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
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
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
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
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
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
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
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
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
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
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
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
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
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
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
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
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
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
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
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
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
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
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

end Itasca.Runtime.Code
