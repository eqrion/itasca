import Itasca.Runtime.Compiler.Local.Source.SourceStacks
import Itasca.Runtime.Compiler.Local.Relations.Local.LocalDeclarations
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerMetadata

/-!
An actual successful final observation establishes operand layout from concrete validator values and the fixed local layout of the resulting compiler.

Main declarations: `compiler_observe_layout_success` and `CompilerStable.local_layout`. A direct consumer is `Compiler.Local.Relations.Control.BranchReachable`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- An actual successful final observation establishes operand layout from
concrete validator values and the fixed local layout of the resulting compiler. -/
theorem compiler_observe_layout_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : code.OpIterState) (known : ConcreteStack state.vals.val) (locals : LocalLayout after)
    (accepted : runtime.compiler.FunctionCompiler.observe ops before state = .ok (.Ok (), after)) :
    CompilerLayout after (Sequence.stackTypes state.vals.val) := by
  obtain ⟨types, concrete⟩ := (concrete_stack_iff state.vals.val).mp known
  have post := compiler_observe ops law before state
  rw [accepted, WP.spec_ok] at post
  obtain ⟨offsets, height, localTypes, localSlots, localOffsets, reachable, code, sources,
    next, capacity, growth, frames, controls⟩ := post rfl
  have decoded : Sequence.stackTypes state.vals.val = types.map Translate.valueType := by
    simp [concrete, Sequence.stackTypes, List.map_map, Function.comp_def]
  rw [decoded]
  refine ⟨locals.slots, locals.offsets, ?_, ?_, capacity⟩
  · rw [offsets, concrete, observed_offsets_values, ← localSlots, locals.slots]
    simp [stackOffsets]
  · rw [height, concrete, observed_height_values, ← localSlots, locals.slots]

/-- Fixed source/local metadata transports local layout independently of the
current operand stack or reachability mode. -/
theorem CompilerStable.local_layout {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (stable : CompilerStable before after) (locals : LocalLayout before) : LocalLayout after := by
  have fields := stable.fields
  obtain ⟨signatures, functions, batch, typeIndex, types, params, slotsEq, start, finish, offsets⟩ := fields
  constructor
  · simpa [compilerLocals, types, slotsEq] using locals.slots
  · simpa [compilerLocals, types, offsets] using locals.offsets
end Itasca.Runtime.Compiler
