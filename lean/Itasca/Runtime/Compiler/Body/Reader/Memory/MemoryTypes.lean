import Itasca.Runtime.Compiler.Body.Reader.Memory.MemoryStacks
import Itasca.Runtime.Compiler.Body.Source.TypedLowering

/-!
Scalar memory operand-stack types and reader availability.

Main declarations: `memory_load_stack_types` and `memory_reader_available`. A direct consumer is `Compiler.Body.Reader.Memory.Acceptance`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem memory_load_stack_types {old next outer segment rest : List code.StackType} {ty : wasm_types.ValueType}
    (known : ConcreteStack old) (oldEq : old = outer ++ segment)
    (shape : segment = rest ++ [.Val .I32]) (nextEq : next = outer ++ rest ++ [.Val ty]) :
    ∃ (front : List valtype) (types : List Itasca.wasm_types.ValueType), Sequence.stackTypes old = front ++ [.I32] ∧
      next = types.map code.StackType.Val ∧ types.map Translate.valueType = front ++ [Translate.valueType ty] := by
  have oldShape : old = (outer ++ rest) ++ [.Val .I32] := by simp [oldEq,shape,List.append_assoc]
  have prefixKnown : ConcreteStack (outer ++ rest) := (concrete_stack_append.mp (oldShape ▸ known)).1
  obtain ⟨types,typesEq⟩ := (concrete_stack_iff _).mp prefixKnown
  refine ⟨types.map Translate.valueType,types ++ [ty],?_,?_,by simp⟩
  · simp [oldShape,typesEq,Sequence.stackTypes,List.map_map,Function.comp_def,Translate.valueType]
  · simpa [List.map_append] using nextEq.trans (by rw [typesEq])

theorem memory_store_stack_types {old next outer segment rest : List code.StackType} {ty : wasm_types.ValueType}
    (known : ConcreteStack old) (oldEq : old = outer ++ segment)
    (shape : segment = rest ++ [.Val .I32,.Val ty]) (nextEq : next = outer ++ rest) :
    ∃ (front : List valtype) (types : List Itasca.wasm_types.ValueType), Sequence.stackTypes old = front ++ [.I32,Translate.valueType ty] ∧
      next = types.map code.StackType.Val ∧ types.map Translate.valueType = front := by
  have oldShape : old = (outer ++ rest) ++ [.Val .I32,.Val ty] := by simp [oldEq,shape,List.append_assoc]
  have prefixKnown : ConcreteStack (outer ++ rest) := (concrete_stack_append.mp (oldShape ▸ known)).1
  obtain ⟨types,typesEq⟩ := (concrete_stack_iff _).mp prefixKnown
  refine ⟨types.map Translate.valueType,types,?_,nextEq.trans typesEq,rfl⟩
  simp [oldShape,typesEq,Sequence.stackTypes,List.map_map,Function.comp_def,Translate.valueType]

theorem memory_reader_available (env : metadata.Env) (arg : code.MemArg) (natural : U32)
    (C : context) (memories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    (accepted : code.check_memory_and_alignment env arg natural = .ok (.Ok ())) :
    ∃ memory, C.MEMS[0]? = some memory := by
  have effect := code.check_memory_and_alignment.spec env arg natural
  rw [accepted,WP.spec_ok] at effect
  have bound : 0 < C.MEMS.length := by simpa [memories] using effect.1
  exact ⟨C.MEMS[0],List.getElem?_eq_getElem bound⟩
end Itasca.Runtime.Compiler
