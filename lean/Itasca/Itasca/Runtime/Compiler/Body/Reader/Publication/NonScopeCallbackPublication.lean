import Itasca.Runtime.Compiler.Body.Reader.Memory.MemoryEmissions
import Itasca.Runtime.Compiler.Body.Reader.Source.SourceOpcodeFamilies
import Itasca.Runtime.Compiler.Local.Coordinates.InstructionTargetEffects
import Itasca.Runtime.Compiler.Local.Publication.ControlMapPublication
import Itasca.Runtime.Compiler.Body.Reader.Scalar.ScalarEffects
import Itasca.Runtime.Compiler.Body.Reader.Float.FloatConstantEmissions
import Itasca.Runtime.Compiler.Body.Reader.Publication.ScalarCallbackPublication
import Itasca.Runtime.Compiler.Body.Reader.Simd.SimdCallbackPublication
import Itasca.Runtime.Compiler.Local.Publication.ScalarAndTablePublication

open WebAssembly

/-!
Proofs for Runtime / Compiler / Body / Reader / Publication.

This module collects MemoryCallbackPublication, NonScopeCallbackPublication.
Each section documents its contracts and consumers.
-/

/-! ## MemoryCallbackPublication -/

section

/-!
# Memory callback publication

Every scalar and packed load/store event preserves source-coordinate and control-map publication bounds. Reader advancement consumes these event-indexed facts.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

/-- Every memory visitor event preserves source-coordinate and control-map
publication bounds, covering all scalar and packed load/store hooks. -/
theorem compiler_memory_hook_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : code.OpIterState) (hook : MemoryHook) (arg : code.MemArg)
    (coordinates : SourceCoordinates before) (maps : ControlMapPublication before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before (.op state (.memory hook arg)) =
      .ok (.Ok (),after)) : SourceCoordinates after ∧ ControlMapPublication after := by
  have range : 40 ≤ hook.opcode.val ∧ hook.opcode.val ≤ 62 := by cases hook <;> decide
  have visited := (MemoryHook.dispatch (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    before state hook arg).trans called
  rcases source_memory_byte_partition hook.opcode range.1 range.2 with ⟨op,byte⟩ | ⟨op,byte⟩
  · have dispatch := (memory_load_reader_facts ops before state op arg).2.2.2.2.1
    rw [← byte,dispatch] at visited
    exact ⟨compiler_memory_load_dispatch_source_coordinates ops law before after state op arg.offset arg.align
      coordinates inside forward visited,
      compiler_core_map_publication ops law before after state (.load op arg.offset arg.align) visited maps forward⟩
  · have dispatch := (memory_store_reader_facts ops before state op arg).2.2.2.2.1
    rw [← byte,dispatch] at visited
    exact ⟨compiler_memory_store_dispatch_source_coordinates ops law before after state op arg.offset arg.align
      coordinates inside forward visited,
      compiler_core_map_publication ops law before after state (.store op arg.offset arg.align) visited maps forward⟩

end Itasca.Compiler

end

/-! ## NonScopeCallbackPublication -/

section

/-!
# Publication through non-scope callbacks

Numeric, extended numeric and ordinary event cases preserve the source-coordinate and control-map bounds used by reader advancement.
-/

/-! ## NumericCallbackPublication -/

section NumericCallbackPublication

/-!
# Numeric callback publication

Numeric event tables select canonical integer/float lowering descriptors. Publication preservation follows from those descriptors rather than a caller-supplied dispatch correspondence.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

/-- Each numeric visitor event selects a canonical integer or float lowering.
This bridges the event table to publication invariants without a caller-supplied
opcode-subset premise. -/
theorem numeric_hook_publication_dispatch {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState) (hook : NumericHook) :
    (∃ op : SourceMachine.Numeric.Instruction,
      invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler (.op state (.numeric hook)) =
        runtime.compiler.lower.FunctionCompiler.op ops compiler state (integerOpcode op) 0#u32 0#u32 0#u128) ∨
    (∃ op : SourceMachine.Float.Instruction,
      invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler (.op state (.numeric hook)) =
        runtime.compiler.lower.FunctionCompiler.op ops compiler state (floatOpcode op) 0#u32 0#u32 0#u128) := by
  have range : 69 ≤ hook.opcode.val ∧ hook.opcode.val < 192 := by cases hook <;> decide
  rcases source_numeric_byte_partition hook.opcode range.1 range.2 with integer | floating
  · obtain ⟨op,byte⟩ := integer_opcode_of_mem integer
    have wordBound := integer_opcode_byte op
    have same := congrArg UScalar.val byte
    have base : (integerOpcode op).val < 192 := by scalar_tac
    obtain ⟨operation,actual,_,selected,_,_,_,dispatch,_⟩ := integer_reader_facts ops compiler state op base
    rw [byte,NumericHook.of_opcode_opcode] at selected
    have equal := Option.some.inj selected
    subst actual
    exact .inl ⟨op,dispatch⟩
  · obtain ⟨op,base,byte⟩ := float_base_opcode_of_mem floating
    obtain ⟨operation,actual,_,selected,_,_,_,dispatch,_⟩ := float_reader_facts ops compiler state op base
    rw [byte,NumericHook.of_opcode_opcode] at selected
    have equal := Option.some.inj selected
    subst actual
    exact .inr ⟨op,dispatch⟩

/-- All actual numeric visitor callbacks preserve both coordinate and map
publication bounds, independently of the integer/float event classification. -/
theorem compiler_numeric_hook_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : code.OpIterState) (hook : NumericHook)
    (coordinates : SourceCoordinates before) (maps : ControlMapPublication before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before (.op state (.numeric hook)) =
      .ok (.Ok (),after)) : SourceCoordinates after ∧ ControlMapPublication after := by
  rcases numeric_hook_publication_dispatch ops before state hook with ⟨op,dispatch⟩ | ⟨op,dispatch⟩
  · rw [dispatch] at called
    exact ⟨compiler_numeric_dispatch_source_coordinates ops law before after state op coordinates inside forward called,
      compiler_numeric_map_publication ops law before after state op called maps forward⟩
  · rw [dispatch] at called
    exact ⟨compiler_float_dispatch_source_coordinates ops law before after state op coordinates inside forward called,
      compiler_float_map_publication ops law before after state op called maps forward⟩

end Itasca.Compiler

end NumericCallbackPublication

/-! ## ExtendedNumericCallbackPublication -/

section ExtendedNumericCallbackPublication

/-!
# Extended numeric publication

Sign-extension and saturating conversion events select exact lowering descriptors. Their publication effects compose with ordinary reader advancement.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

/-- Sign-extension and saturating numeric events select exact descriptors. -/
theorem extended_numeric_hook_publication_dispatch {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState) (hook : ExtendedNumericHook) :
    (∃ op : SourceMachine.Numeric.Instruction,
      invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler (.op state (.extendedNumeric hook)) =
        runtime.compiler.lower.FunctionCompiler.op ops compiler state (integerOpcode op) 0#u32 0#u32 0#u128) ∨
    (∃ op : SourceMachine.Float.Instruction,
      invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler (.op state (.extendedNumeric hook)) =
        runtime.compiler.lower.FunctionCompiler.op ops compiler state (floatOpcode op) 0#u32 0#u32 0#u128) := by
  cases hook
  · exact .inl ⟨.unary .I32 .extend8,rfl⟩
  · exact .inl ⟨.unary .I32 .extend16,rfl⟩
  · exact .inl ⟨.unary .I64 .extend8,rfl⟩
  · exact .inl ⟨.unary .I64 .extend16,rfl⟩
  · exact .inl ⟨.unary .I64 .extend32,rfl⟩
  · exact .inr ⟨.truncate .F32 .I32 .S true,rfl⟩
  · exact .inr ⟨.truncate .F32 .I32 .U true,rfl⟩
  · exact .inr ⟨.truncate .F64 .I32 .S true,rfl⟩
  · exact .inr ⟨.truncate .F64 .I32 .U true,rfl⟩
  · exact .inr ⟨.truncate .F32 .I64 .S true,rfl⟩
  · exact .inr ⟨.truncate .F32 .I64 .U true,rfl⟩
  · exact .inr ⟨.truncate .F64 .I64 .S true,rfl⟩
  · exact .inr ⟨.truncate .F64 .I64 .U true,rfl⟩

/-- Every sign-extension and saturating callback preserves both publication invariants. -/
theorem compiler_extended_numeric_hook_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : code.OpIterState) (hook : ExtendedNumericHook)
    (coordinates : SourceCoordinates before) (maps : ControlMapPublication before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before (.op state (.extendedNumeric hook)) =
      .ok (.Ok (),after)) : SourceCoordinates after ∧ ControlMapPublication after := by
  rcases extended_numeric_hook_publication_dispatch ops before state hook with ⟨op,dispatch⟩ | ⟨op,dispatch⟩
  · rw [dispatch] at called
    exact ⟨compiler_numeric_dispatch_source_coordinates ops law before after state op coordinates inside forward called,
      compiler_numeric_map_publication ops law before after state op called maps forward⟩
  · rw [dispatch] at called
    exact ⟨compiler_float_dispatch_source_coordinates ops law before after state op coordinates inside forward called,
      compiler_float_map_publication ops law before after state op called maps forward⟩

end Itasca.Compiler

end ExtendedNumericCallbackPublication

/-! ## NonScopeCallbackPublication -/

section NonScopeCallbackPublication

/-!
# Publication outside scope boundaries

Events that neither open nor close control frames preserve publication without new frame geometry. ELSE retains its existing map owner; action-range predicates classify these cases.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

/-- Visitor events whose publication preservation does not require new or
closing frame geometry. ELSE retains the current map owner. -/
inductive NonScopePublicationAction : Action → Prop where
  | scalar {action} (supported : ScalarPublicationAction action) : NonScopePublicationAction action
  | numeric (hook : NumericHook) : NonScopePublicationAction (.numeric hook)
  | extendedNumeric (hook : ExtendedNumericHook) : NonScopePublicationAction (.extendedNumeric hook)
  | memory (hook : MemoryHook) (arg : code.MemArg) : NonScopePublicationAction (.memory hook arg)
  | simd {action} (supported : SimdPublicationAction action) : NonScopePublicationAction action
  | unreachable : NonScopePublicationAction .unreachable
  | return_ : NonScopePublicationAction .return_
  | br (depth : U32) (types : signature.ResultType) : NonScopePublicationAction (.br depth types)
  | br_if (depth : U32) (types : signature.ResultType) : NonScopePublicationAction (.br_if depth types)
  | label (depth : U32) : NonScopePublicationAction (.br_table_label depth)
  | table (fallback : U32) (types : signature.ResultType) : NonScopePublicationAction (.br_table fallback types)
  | else_ (bt : signature.BlockType) : NonScopePublicationAction (.else_ bt)

/-- Actual non-scope-boundary callbacks preserve both publication invariants.
No stack typing, accepted future trace, or completed code certificate is used. -/
theorem compiler_non_scope_hook_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : code.OpIterState) {action : Action} (supported : NonScopePublicationAction action)
    (coordinates : SourceCoordinates before) (maps : ControlMapPublication before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before (.op state action) =
      .ok (.Ok (),after)) : SourceCoordinates after ∧ ControlMapPublication after := by
  cases supported with
  | scalar supported => exact compiler_scalar_hook_publication ops law before after state supported coordinates maps inside forward called
  | numeric hook => exact compiler_numeric_hook_publication ops law before after state hook coordinates maps inside forward called
  | extendedNumeric hook => exact compiler_extended_numeric_hook_publication ops law before after state hook coordinates maps inside forward called
  | memory hook arg => exact compiler_memory_hook_publication ops law before after state hook arg coordinates maps inside forward called
  | simd supported => exact compiler_simd_hook_publication ops law before after state supported coordinates maps inside forward called
  | unreachable =>
    exact ⟨compiler_unreachable_source_coordinates ops law before after state coordinates inside forward called,
      compiler_unreachable_map_publication ops law before after state maps forward called⟩
  | return_ =>
    exact ⟨compiler_return_source_coordinates ops law before after state coordinates inside forward called,
      compiler_return_map_publication ops law before after state maps forward called⟩
  | br depth types =>
    exact ⟨compiler_br_source_coordinates ops law before after state depth types coordinates inside forward called,
      compiler_br_map_publication ops law before after state depth types maps forward called⟩
  | br_if depth types =>
    exact ⟨compiler_br_if_source_coordinates ops law before after state depth types coordinates inside forward called,
      compiler_br_if_map_publication ops law before after state depth types maps forward called⟩
  | label depth =>
    exact ⟨compiler_table_label_source_coordinates ops law before after state depth coordinates called,
      compiler_table_label_map_publication ops law before after state depth maps called⟩
  | table fallback types =>
    exact ⟨compiler_br_table_source_coordinates ops law before after state fallback types coordinates inside forward called,
      compiler_br_table_map_publication ops law before after state fallback types maps forward called⟩
  | else_ bt =>
    exact ⟨compiler_else_source_coordinates ops law before after state bt coordinates inside forward called,
      compiler_else_map_publication ops law before after state bt maps forward called⟩

/-- The source SIMD interval is an independent bound on event arguments. -/
def PublicationActionRange : Action → Prop
  | .simd sub | .simd_lane sub _ | .simd_memory sub _ | .simd_memory_lane sub _ _ => sub.val < 256
  | _ => True

/-- Entry and END require the separate frame-geometry adapters. -/
def NoScopeBoundary : Action → Prop
  | .block _ | .loop _ | .if_ _ | .end_ _ _ => False
  | _ => True

/-- Exhaustive event coverage outside the four scope-boundary forms. The only
numerical restriction is the independent Wasm 2 SIMD subopcode interval. -/
theorem NonScopePublicationAction.of_range (action : Action)
    (range : PublicationActionRange action) (ordinary : NoScopeBoundary action) :
    NonScopePublicationAction action := by
  cases action <;> simp only [PublicationActionRange,NoScopeBoundary] at range ordinary
  all_goals first
  | contradiction
  | solve | (apply NonScopePublicationAction.scalar; constructor)
  | exact .numeric _
  | exact .extendedNumeric _
  | exact .memory _ _
  | solve | (apply NonScopePublicationAction.simd; constructor <;> exact range)
  | exact .unreachable
  | exact .return_
  | exact .br _ _
  | exact .br_if _ _
  | exact .label _
  | exact .table _ _
  | exact .else_ _

end Itasca.Compiler

end NonScopeCallbackPublication

end
