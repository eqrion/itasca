import Exec.Code.Body.Control.Common.StructuredCompilerPrefix
import Exec.Code.Body.Control.Common.StructuredPrefixDead
import Exec.Code.Local.Relations.Common.StatefulEmissionTransport
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Pair metadata may grow while a source prefix is open. Quantifying over its
future suffix keeps the continuation's emission relation fixed at each use. -/
def CumulativeCompilerPrefix {A : Type} (C : context)
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (raw : List code.StackType) (position : Nat) : Prop :=
  ∀ future : List (U32 × U32),
    StructuredCompilerPrefix (CumulativeEmission (compiler.function.indirect.val ++ future) C)
      initial compiler types functions returns locals parents current raw position

theorem CumulativeCompilerPrefix.current {A : Type} {C}
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {types functions returns locals parents current raw position}
    (invariant : CumulativeCompilerPrefix C initial compiler types functions returns locals parents current raw position) :
    StructuredCompilerPrefix (CumulativeEmission compiler.function.indirect.val C)
      initial compiler types functions returns locals parents current raw position := by
  simpa only [List.append_nil] using invariant []

/-- One actual pair-table append changes only which future suffix is supplied
to the old prefix; no backwards conversion of continuations is required. -/
theorem CumulativeCompilerPrefix.ordinary {A : Type} {C}
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals parents current raw position nextRaw nextPosition instruction emitted output}
    (invariant : CumulativeCompilerPrefix C initial before types functions returns locals parents current raw position)
    (reachable : before.reachable = true)
    (ordinary : CompilerOrdinaryStable before after)
    (lowered : TypedLowered before after nextRaw emitted output)
    (emission : StatefulEmission after.function.indirect.val C (Sequence.stackTypes raw) instruction [emitted] output)
    (extra : List (U32 × U32)) (pairs : after.function.indirect.val = before.function.indirect.val ++ extra)
    (sources : SourceProgress before after) (consumed : position < nextPosition)
    (cursor : after.next_source.val ≤ nextPosition) :
    CumulativeCompilerPrefix C initial after types functions returns locals parents (current.advance instruction) nextRaw nextPosition := by
  intro future
  have prior : StructuredCompilerPrefix (CumulativeEmission (after.function.indirect.val ++ future) C)
      initial before types functions returns locals parents current raw position := by
    simpa only [pairs,List.append_assoc] using invariant (extra ++ future)
  apply prior.ordinary reachable ordinary lowered (.right (emission.map_pairs ?_)) sources consumed cursor
  intro index pair found
  have bound := (List.getElem?_eq_some_iff.mp found).1
  simpa only [List.getElem?_append,if_pos bound] using found

theorem CumulativeCompilerPrefix.skip {A : Type} {C}
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals parents current raw position nextRaw nextPosition}
    (invariant : CumulativeCompilerPrefix C initial before types functions returns locals parents current raw position)
    (instruction : instr) (dead : before.reachable = false) (deadAfter : after.reachable = false)
    (ordinary : CompilerOrdinaryStable before after) (unchanged : after.function.code = before.function.code)
    (pairs : after.function.indirect = before.function.indirect)
    (sources : SourceProgress before after) (consumed : position < nextPosition)
    (cursor : after.next_source.val ≤ nextPosition) :
    CumulativeCompilerPrefix C initial after types functions returns locals parents (current.advance instruction) nextRaw nextPosition := by
  intro future
  simpa only [pairs] using (invariant future).skip instruction dead deadAfter ordinary unchanged sources consumed cursor

end Exec.Code
