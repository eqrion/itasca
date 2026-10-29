import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalTerminal
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FramePlanPop
import Itasca.Runtime.Compiler.Local.Relations.Prefix.PrefixZipper
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ResolvedGuards

/-!
An unentered source subtree emits no executable body. Its enclosing terminal prefix remains retained; no code relation is asserted for the child.

Main declarations: `UniversalDormant`. A direct consumer is `Compiler.Local.Control.Table.StructuredUniversalDormant`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- An unentered source subtree emits no executable body. Its enclosing
terminal prefix remains retained; no code relation is asserted for the child. -/
structure UniversalDormant {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope) : Prop where
  unentered : current.entered = false
  localsEq : compilerLocals compiler = locals
  sites : ∀ frame ∈ compiler.frames.val, FrameSites compiler.function.code.val frame
  prefixes : ∀ label labels groups,
    FramePlans compiler.function.code.val.length locals compiler.frames.val (label :: labels) groups →
    ScopeLabel current label → List.Forall₂ ScopeLabel parents.reverse labels →
    ParentPrefixes types functions returns locals (resolvedCode compiler.function.code.val groups)
      parents labels current

end Itasca.Runtime.Compiler
