import Exec.Code.Body.Control.Common.StructuredCompilerPrefixAdvance
import Exec.Code.Local.Relations.Common.CoreEmission
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- A syntactic inclusion of the existing pure bytecode emission cases. -/
def LinearEmbedding (locals : List valtype)
    (emit : List valtype → instr → List Bytecode → List valtype → Prop) : Prop :=
  ∀ {input instruction code output}, LinearEmission locals input instruction code output → emit input instruction code output

theorem CoreEmission.linearEmbedding (C : context) : LinearEmbedding C.LOCALS (CoreEmission C) := by
  intro input instruction code output emission
  exact .pure emission

theorem StructuredCompilerPrefix.ordinary_linear {A : Type}
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position nextRaw nextPosition instruction emitted output}
    (invariant : StructuredCompilerPrefix emit initial before types functions returns locals parents current raw position)
    (embedding : LinearEmbedding locals emit)
    (reachable : before.reachable = true) (ordinary : CompilerOrdinaryStable before after)
    (lowered : TypedLowered before after nextRaw emitted output)
    (emission : LinearEmission locals (Sequence.stackTypes raw) instruction [emitted] output)
    (sources : SourceProgress before after) (consumed : position < nextPosition)
    (cursor : after.next_source.val ≤ nextPosition) :
    StructuredCompilerPrefix emit initial after types functions returns locals parents (current.advance instruction) nextRaw nextPosition :=
  invariant.ordinary reachable ordinary lowered (embedding emission) sources consumed cursor

theorem StructuredCompilerPrefix.ordinary_empty_linear {A : Type}
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position nextRaw nextPosition instruction output}
    (invariant : StructuredCompilerPrefix emit initial before types functions returns locals parents current raw position)
    (embedding : LinearEmbedding locals emit)
    (reachable : before.reachable = true) (ordinary : CompilerOrdinaryStable before after)
    (lowered : TypedLoweredEmpty before after nextRaw output)
    (emission : LinearEmission locals (Sequence.stackTypes raw) instruction [] output)
    (sources : SourceProgress before after) (consumed : position < nextPosition)
    (cursor : after.next_source.val ≤ nextPosition) :
    StructuredCompilerPrefix emit initial after types functions returns locals parents (current.advance instruction) nextRaw nextPosition :=
  invariant.ordinary_empty reachable ordinary lowered (embedding emission) sources consumed cursor
end Exec.Code
