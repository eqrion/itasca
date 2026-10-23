import Exec.Code.Body.Control.Common.StructuredLinearEmbedding
import Exec.Code.Body.Control.Table.StructuredCompilerPrefixAdvance
import Exec.Code.Local.Control.Table.StructuredCodeTableExclusion
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem StructuredCompilerPrefix.ordinary_linear {jumpTables : List U32} {A : Type}
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position nextRaw nextPosition instruction emitted output}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (embedding : LinearEmbedding locals emit)
    (reachable : before.reachable = true) (ordinary : CompilerOrdinaryStable before after)
    (lowered : TypedLowered before after nextRaw emitted output)
    (emission : LinearEmission locals (Sequence.stackTypes raw) instruction [emitted] output)
    (sources : SourceProgress before after) (consumed : position < nextPosition)
    (cursor : after.next_source.val ≤ nextPosition) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance instruction) nextRaw nextPosition :=
  invariant.ordinary reachable ordinary lowered (embedding emission) sources consumed cursor emission.not_branchTable

theorem StructuredCompilerPrefix.ordinary_empty_linear {jumpTables : List U32} {A : Type}
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position nextRaw nextPosition instruction output}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (embedding : LinearEmbedding locals emit)
    (reachable : before.reachable = true) (ordinary : CompilerOrdinaryStable before after)
    (lowered : TypedLoweredEmpty before after nextRaw output)
    (emission : LinearEmission locals (Sequence.stackTypes raw) instruction [] output)
    (sources : SourceProgress before after) (consumed : position < nextPosition)
    (cursor : after.next_source.val ≤ nextPosition) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance instruction) nextRaw nextPosition :=
  invariant.ordinary_empty reachable ordinary lowered (embedding emission) sources consumed cursor emission.not_branchTable
end Exec.Code
