import Itasca.Runtime.Compiler.Body.Callbacks.Prefix.CompilerPrefix
import Itasca.Runtime.Compiler.Local.Control.Segments.Structured
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredComposition
import Itasca.Runtime.Compiler.Local.Relations.Prefix.Concatenation
import Itasca.Runtime.Compiler.Local.Relations.Prefix.Extension
import Itasca.Runtime.Compiler.Local.Relations.Prefix.PrefixZipper
import Itasca.Runtime.Compiler.Local.Relations.Prefix.Prefix
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ResolvedPrefix
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalPrefix
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalTerminal
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalDormant
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerDeadMetadata
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulEmissionTransport
import Itasca.Runtime.Compiler.Body.Reader.Control.Boundary
import Itasca.Runtime.Compiler.Body.Reader.Control.ScopeFronts
import Itasca.Runtime.Compiler.Body.Reader.Control.ReachabilitySteps
import Itasca.Runtime.Compiler.Body.Reader.Control.KnownFronts
import Itasca.Runtime.Compiler.Body.Reader.Replay.PostDeclared
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackIndirect
import Itasca.Runtime.Compiler.Body.Reader.Control.EnterWasm2
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchWasm2
import Itasca.Runtime.Compiler.Body.Reader.Control.CloseWasm2
import Itasca.Runtime.Compiler.Local.Relations.Syntax.ReaderOpcode
import Itasca.Runtime.Compiler.Body.Reader.Control.ControlBoundary
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FramePlanPop
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseFrames
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.ScopeCallbackEnter
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlEntrySuccess
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerEnterMetadata
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlCursor
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlSources
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlObservedLayout
import Itasca.Runtime.Compiler.Body.Callbacks.Calls.ScopeCallbackInputs
import Itasca.Runtime.Compiler.Body.Reader.Control.Reachability
import Itasca.Runtime.Compiler.Body.Reader.Control.FrontTransitions
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.ScopeCallbackDead
import Itasca.Runtime.Compiler.Local.Relations.Stacks.KnownPopStack
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.ScopeCallbackIf
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchLayout
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalConditional
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseEvidence
import Itasca.Runtime.Compiler.Local.Relations.Calls.BranchSuccessCallbacks
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchSuccessControls
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CompilerCallbackMetadata
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackSources
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackCursor
import Itasca.Runtime.Compiler.Body.Reader.Replay.Post
import Itasca.Runtime.Compiler.Local.Source.SourceStacks
import Itasca.Runtime.Compiler.Body.Reader.Replay.Span
import Itasca.Runtime.Compiler.Body.Relations.Control.BranchIfLayout
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchReachable
import Itasca.Runtime.Compiler.Local.Relations.Calls.BranchSuccessConditionalCallbacks
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseSource
import Itasca.Runtime.Compiler.Body.Reader.Control.KnownFrontEntry
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ScopeFrameSelect
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchEffects
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FramePlanUpdate
import Itasca.Runtime.Compiler.Local.Relations.Control.ResolvedBranchPrefix
import Itasca.Runtime.Compiler.Local.Control.Control.UniversalBranch
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ResolvedConditionalPrefix
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseTransition
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ResolvedGuards
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ScopeStackElse
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ScopeStackClose
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EnterElse
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerCloseMetadata
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlMapCounts
import Itasca.Runtime.Compiler.Local.Relations.Control.KnownControlStack
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseSuccess
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalRoot
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CloseGuardedScope
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ResolvedLiteral
import Itasca.Runtime.Compiler.Body.Reader.Control.EndSignature
import Itasca.Runtime.Compiler.Local.Callbacks.Function.CloseFunction
import Itasca.Runtime.Compiler.Local.Relations.Function.Function
import Itasca.Runtime.Compiler.Local.Relations.Prefix.LabelWiden
import Itasca.Runtime.Compiler.Local.Source.TypedRunClosed
import Itasca.Runtime.Compiler.Body.Reader.Stacks.Stacks
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
