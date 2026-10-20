import Exec.Code.Body.Reader.Publication.ScalarCallbackPublication
import Exec.Code.Body.Reader.Publication.NumericCallbackPublication
import Exec.Code.Body.Reader.Publication.ExtendedNumericCallbackPublication
import Exec.Code.Body.Reader.Memory.MemoryCallbackPublication
import Exec.Code.Body.Reader.Simd.SimdCallbackPublication
import Exec.Code.Local.Coordinates.CallbackSourceCoordinates
import Exec.Code.Local.Coordinates.TableSourceCoordinates
import Exec.Code.Local.Publication.CallbackMapPublication
import Exec.Code.Local.Publication.TableMapPublication
import Exec.Code.Local.Publication.ElseMapPublication

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

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

end Exec.Code
