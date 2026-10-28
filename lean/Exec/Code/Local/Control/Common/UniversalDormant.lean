import Exec.Code.Local.Control.Common.UniversalTerminal
import Exec.Code.Local.Callbacks.Common.FramePlanPop
import Exec.Code.Local.Relations.Common.PrefixZipper
import Exec.Code.Local.Relations.Common.ResolvedGuards
namespace Itasca.Runtime.Code
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

end Itasca.Runtime.Code
