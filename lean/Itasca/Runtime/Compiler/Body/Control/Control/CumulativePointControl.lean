import Itasca.Runtime.Compiler.Body.Callbacks.Prefix.CompilerPrefixStart
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Compiler.Local.Relations.Prefix.SuspendedPrefix
import Itasca.Runtime.Compiler.Local.Relations.Prefix.PrefixZipper
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalPrefix
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalDormant
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulLowered
import Itasca.Runtime.Compiler.Body.Reader.Control.Reachability
import Itasca.Runtime.Compiler.Body.Reader.Control.Return
import Itasca.Runtime.Compiler.Body.Reader.Replay.MetadataTypes
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CompilerCodeMonotoneCallbacks
import Itasca.Runtime.Compiler.Body.Reader.Control.ScopeWasm2
import Itasca.Runtime.Compiler.Body.Reader.Control.FrontTransitions
import Itasca.Runtime.Compiler.Local.Relations.Syntax.ReaderOpcode
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupBudget
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseFrames
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlObservedLayout
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchCertificates
import Itasca.Runtime.Compiler.Body.Callbacks.Calls.ScopeCallbackInputs
import Itasca.Runtime.Compiler.Local.Relations.Stacks.KnownNumericStack
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalRoot
import Itasca.Runtime.Compiler.Local.Relations.Calls.IndirectCallMetadata
import Itasca.Runtime.Compiler.Body.Reader.Replay.Post
import Itasca.Runtime.Compiler.Local.Source.SourceStacks
import Itasca.Runtime.Compiler.Body.Relations.Control.BranchIfLayout
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CompilerCodeMonotoneControl
import Itasca.Runtime.Compiler.Local.Relations.Control.ResolvedBranchPrefix
import Itasca.Runtime.Compiler.Local.Control.Control.StructuredElseResolvedAppend
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ConsumedPrefix
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ResolvedGuards
import Itasca.Runtime.Compiler.Local.Relations.Control.KnownControlStack
import Itasca.Runtime.Compiler.Local.Callbacks.Function.CloseFunction
import Itasca.Runtime.Compiler.Local.Relations.Function.Function
import Itasca.Runtime.Compiler.Local.Source.TypedRunClosed
import Itasca.Runtime.Compiler.Body.Reader.Stacks.Values

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem ReaderBoundaryWasm2.root_iff {data env locals index ft st parents current}
    (boundary : ReaderBoundaryWasm2 data env locals index ft st parents current) :
    current.form = .body ↔ st.blocks.val.length = 1 := by
  obtain ⟨C,outer,spine,header,base,typed,controls,blocks,values⟩ := boundary.opened
  constructor
  · intro form
    have empty := (form ▸ spine).body.1
    simp [blocks,empty]
  · intro count
    have empty : parents = [] := by simpa [blocks] using count
    generalize formEq : current.form = form at spine ⊢
    cases spine with
    | root => rfl
    | push => simp at empty

end Itasca.Runtime.Compiler
