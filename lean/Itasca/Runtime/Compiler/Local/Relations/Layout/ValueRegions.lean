import Itasca.Runtime.Compiler.Local.Source.SourceStacks
import Itasca.Runtime.Compiler.Local.Relations.Local.LocalDeclarations
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Representation.Values

/-!
Sections, each formerly its own module: ObservationLayout, ValueRegions.
-/

/-! ## ObservationLayout -/

section

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

end

/-! ## ValueRegions -/

section

/-! Local value boundaries in the mathematical word encoding. These lemmas
apply uniformly to one-word scalar/reference values and two-word vectors. -/
namespace Itasca.Runtime.Compiler

theorem encode_values_drop (values : List val) (count : Nat) :
    (encodeValues values).drop (offset (values.map valueType) count) =
      encodeValues (values.drop count) := by
  have hs := encode_values_append (values.take count) (values.drop count)
  rw [List.take_append_drop] at hs
  rw [hs]
  have hl : offset (values.map valueType) count = (encodeValues (values.take count)).length := by
    rw [encode_values_length]
    simp only [offset, List.map_take]
  rw [hl, List.drop_left]

theorem encode_values_lookup {values : List val} {index : Nat} {value : val}
    (lookup : values[index]? = some value) :
    ((encodeValues values).drop (offset (values.map valueType) index)).take
      (width (valueType value)) = encodeValue value := by
  rw [encode_values_drop]
  have bound : index < values.length := List.getElem?_eq_some_iff.mp lookup |>.1
  have hv : values[index] = value := List.getElem?_eq_some_iff.mp lookup |>.2
  rw [List.drop_eq_getElem_cons bound, hv]
  change (encodeValue value ++ encodeValues (values.drop (index + 1))).take _ = _
  rw [← encode_value_length, List.take_left]

theorem encode_values_set {values : List val} {index : Nat} (bound : index < values.length)
    (replacement : val) :
    encodeValues (values.set index replacement) =
      (encodeValues values).take (offset (values.map valueType) index) ++
      encodeValue replacement ++
      (encodeValues values).drop (offset (values.map valueType) (index + 1)) := by
  rw [encode_values_take, encode_values_drop]
  rw [List.set_eq_take_append_cons_drop]
  simp only [bound, ↓reduceIte, encodeValues, List.flatMap_append, List.flatMap_cons, List.append_assoc]

/-- Replacing a local with the same type preserves all local offsets. -/
theorem value_types_set {values : List val} {index : Nat} {old replacement : val}
    (lookup : values[index]? = some old) (typed : valueType replacement = valueType old) :
    (values.set index replacement).map valueType = values.map valueType := by
  rw [List.map_set, typed]
  have hm : (values.map valueType)[index]? = some (valueType old) := by
    simpa using congrArg (Option.map valueType) lookup
  have hb := (List.getElem?_eq_some_iff.mp hm).1
  have hv := (List.getElem?_eq_some_iff.mp hm).2
  rw [← hv]
  exact List.set_getElem_self hb

end Itasca.Runtime.Compiler

end
