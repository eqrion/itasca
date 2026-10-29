import Itasca.Runtime.Compiler.Local.Relations.Prefix.PrefixZipper
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FrameSites
import Itasca.Runtime.Compiler.Local.Relations.Prefix.Prefix
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ResolvedPrefix

/-!
Append one source instruction to the current open scope. Its saved entry, control signature, and physical branch coordinates do not change.

Main declarations: `SourceScope.advance` and `UniversalPrefix`. A direct consumer is `Compiler.Local.Control.Prefix.UniversalTerminal`.
-/

namespace Itasca.Runtime.Code
open Aeneas.Std

/-- Append one source instruction to the current open scope. Its saved entry,
control signature, and physical branch coordinates do not change. -/
def SourceScope.advance (scope : SourceScope) (instruction : instr) : SourceScope :=
  { scope with source := scope.source ++ [instruction] }

/-- The live prefix invariant is uniform over every admissible future layout.
The source zipper fixes exact label types; the plans supply only future PCs and
exit liveness. This component retains no execution-correctness premise. -/
structure UniversalPrefix {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope) (stack : List valtype) : Prop where
  localsEq : compilerLocals compiler = locals
  layout : CompilerLayout compiler stack
  sites : ∀ frame ∈ compiler.frames.val, FrameSites compiler.function.code.val frame
  prefixes : ∀ label labels groups,
    FramePlans compiler.function.code.val.length locals compiler.frames.val (label :: labels) groups →
    ScopeLabel current label → List.Forall₂ ScopeLabel parents.reverse labels →
    ParentPrefixes types functions returns locals (resolvedCode compiler.function.code.val groups)
      parents labels current ∧
    CodePrefix types functions returns locals (resolvedCode compiler.function.code.val groups)
      (label :: labels) current.input current.source current.bodyPc compiler.function.code.val.length stack

end Itasca.Runtime.Code
