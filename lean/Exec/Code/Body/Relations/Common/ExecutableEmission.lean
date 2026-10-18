import Exec.Code.Body.Lowering.Simd.SimdCumulativeEmission
import Exec.Code.Body.Control.Common.CumulativeEmbedding
import Exec.Code.Local.Source.TypedSelectEmission
namespace Exec.Code
open Aeneas.Std

/-- Complete ordinary emission syntax and the branch-table control gate.
A branch-table gate can only enter StructuredCodeWithTables through its
structural constructor, which retains the actual target-table layout. -/
inductive ExecutableEmission (tables : CompilerTables) (C : context) :
    List valtype → instr → List Bytecode → List valtype → Prop where
  | base {before source emitted after}
      (head : SimdCumulativeEmission tables C before source emitted after) :
      ExecutableEmission tables C before source emitted after
  | typedSelect {before source emitted after}
      (head : TypedSelectEmission C before source emitted after) :
      ExecutableEmission tables C before source emitted after
  | branchTable (stack : List valtype) (depths : List labelidx) (fallback : labelidx)
      (selector start len : U32) :
      ExecutableEmission tables C (stack ++ [.I32]) (.BR_TABLE depths fallback)
        [.JumpTable selector start len] stack

instance (tables C) : FloatEmbedding C (ExecutableEmission tables C) :=
  ⟨fun head => .base (.left (.left head))⟩
instance (tables C) : CoreEmbedding C (ExecutableEmission tables C) :=
  ⟨fun head => .base (.left (.left (.core head)))⟩
instance (tables C) : CumulativeEmbedding tables.indirect C (ExecutableEmission tables C) :=
  ⟨fun head => .base (.left head)⟩
instance (tables C) : SimdEmbedding tables.simd tables.constants C (ExecutableEmission tables C) :=
  ⟨fun head => .base (.right head)⟩

theorem ExecutableEmission.append_tables {tables C before source emitted after}
    (head : ExecutableEmission tables C before source emitted after) (extra : CompilerTables) :
    ExecutableEmission (tables.append extra) C before source emitted after := by
  cases head with
  | base h => exact .base (h.append_tables extra)
  | typedSelect h => exact .typedSelect h
  | branchTable => exact .branchTable _ _ _ _ _ _
end Exec.Code
