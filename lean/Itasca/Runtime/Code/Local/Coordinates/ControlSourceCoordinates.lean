import Itasca.Runtime.Code.Local.Coordinates.SourceCoordinateTactic

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- Opening a structured frame emits only at the current source origin. -/
theorem compiler_enter_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (blockType : Itasca.signature.BlockType)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.control.FunctionCompiler.enter ops before state kind blockType = .ok (.Ok (),after)) :
    SourceCoordinates after := by
  unfold runtime.compiler.control.FunctionCompiler.enter at called
  repeat' coordinates_step called using ops, law

/-- Branch stubs, copies, and patching retain source-coordinate order. -/
theorem compiler_branch_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool) (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (called : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (.Ok (),after)) :
    SourceCoordinates after := by
  cases conditional <;>
    simp only [runtime.compiler.control.FunctionCompiler.branch,Bool.false_eq_true,ite_false,ite_true] at called <;>
    repeat' coordinates_step called using ops, law

/-- Closing source scopes patches control targets and emits the root return
at the same source origin as every other instruction in the callback. -/
theorem compiler_end_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (blockType : Itasca.signature.BlockType)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end
      ops before state kind blockType = .ok (.Ok (),after)) : SourceCoordinates after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end at called
  repeat' coordinates_step called using ops, law

/-- Else-arm jumps and their patched destinations retain coordinate order. -/
theorem compiler_else_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (blockType : Itasca.signature.BlockType)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else
      ops before state blockType = .ok (.Ok (),after)) : SourceCoordinates after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else at called
  repeat' coordinates_step called using ops, law

end Itasca.Runtime.Code
