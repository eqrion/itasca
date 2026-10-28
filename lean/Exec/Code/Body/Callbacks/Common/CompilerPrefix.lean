import Exec.Code.Local.Callbacks.Control.ScopeConditions
import Exec.Code.Local.Relations.Common.DormantFrames
import Exec.Code.Body.Source.TypedLowering
import Exec.Code.Local.Callbacks.Common.CompilerOrdinaryMetadata
import Exec.Code.Local.Callbacks.Control.ScopeFrameStack
import Exec.Code.Local.Source.SourceControlBudget
import Exec.Code.Local.Source.SourceLengths
import Exec.Code.Local.Control.Common.UniversalDormant
import Exec.Code.Local.Callbacks.Control.ElseEvidence
import Exec.Code.Local.Control.Common.UniversalPrefix
import Exec.Code.Local.Lowering.Common.LoweringEmpty
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Reachability selects a retained executable prefix, a terminal prefix, or
an unentered subtree. No continuation is assumed for an omitted subtree. -/
inductive PrefixMode {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope) (stack : List valtype) : Prop where
  | live (reachable : compiler.reachable = true) (entered : current.entered = true)
      (retained : UniversalPrefix compiler types functions returns locals parents current stack)
  | terminal (reachable : compiler.reachable = false) (entered : current.entered = true)
      (retained : UniversalTerminal compiler types functions returns locals parents current)
  | dormant (reachable : compiler.reachable = false)
      (retained : UniversalDormant compiler types functions returns locals parents current)

/-- The retained compiler invariant at an actual source-reader boundary. Its
components concern source syntax, physical frames, emitted code, and byte/slot
accounting; none assumes execution correctness. -/
structure CompilerPrefix {A : Type} (initial compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (raw : List code.StackType) (position : Nat) : Prop where
  metadata : CompilerStable initial compiler
  frames : ScopeFrameStack locals compiler parents current
  entryChain : SourceEntryChain parents current
  dormant : DormantFrames compiler.frames.val
  conditions : ScopeConditions locals parents current
  known : ConcreteStack raw
  mode : PrefixMode compiler types functions returns locals parents current (Sequence.stackTypes raw)
  arms : UniversalElse compiler types functions returns locals parents current
  sources : SourceAligned compiler
  codeBudget : SourceCodeBudget compiler position
  controlBudget : SourceControlBudget compiler position
  cursor : compiler.next_source.val ≤ position

end Itasca.Runtime.Code
