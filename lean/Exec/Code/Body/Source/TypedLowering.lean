import Exec.Code.Body.Reader.Common.ReaderValues
import Exec.Code.Local.Lowering.Common.LoweringEmpty
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- The exact concrete source types of the validator's complete operand stack. -/
structure SourceStack (raw : List code.StackType) (types : List valtype) : Prop where
  concrete : ConcreteStack raw
  decoded : Sequence.stackTypes raw = types

theorem SourceStack.of_map {raw : List code.StackType} {types : List valtype}
    (values : List Itasca.types.ValueType) (concrete : raw = values.map code.StackType.Val)
    (decoded : values.map Translate.valueType = types) : SourceStack raw types := by
  refine ⟨(concreteStack_iff raw).mpr ⟨values, concrete⟩, ?_⟩
  simpa only [concrete, Sequence.stackTypes, List.map_map, Function.comp_def] using decoded

theorem SourceStack.unique {raw first second} (left : SourceStack raw first) (right : SourceStack raw second) :
    first = second := left.decoded.symm.trans right.decoded

/-- Actual lowering plus the exact post-reader type vector. Word offsets alone
would not distinguish source types that share the same machine width. -/
def TypedLowered {A : Type} (before after : runtime.compiler.FunctionCompiler A)
    (raw : List code.StackType) (instruction : Bytecode) (stack : List valtype) : Prop :=
  Lowered before after instruction stack ∧ SourceStack raw stack

def TypedLoweredEmpty {A : Type} (before after : runtime.compiler.FunctionCompiler A)
    (raw : List code.StackType) (stack : List valtype) : Prop :=
  LoweredEmpty before after stack ∧ SourceStack raw stack

end Exec.Code
