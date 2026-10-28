import Itasca.Runtime.Code.Body.Callbacks.Common.CompilerPrefix
import Itasca.Runtime.Code.Local.Control.Common.Structured
import Itasca.Runtime.Code.Local.Control.Common.StructuredComposition
import Itasca.Runtime.Code.Local.Relations.Common.Concatenation
import Itasca.Runtime.Code.Local.Relations.Common.Extension
import Itasca.Runtime.Code.Local.Relations.Common.PrefixZipper
import Itasca.Runtime.Code.Local.Relations.Common.Prefix
import Itasca.Runtime.Code.Local.Relations.Common.ResolvedPrefix
import Itasca.Runtime.Code.Local.Control.Common.UniversalPrefix
import Itasca.Runtime.Code.Local.Control.Common.UniversalTerminal
import Itasca.Runtime.Code.Local.Control.Common.UniversalDormant
import Itasca.Runtime.Code.Local.Callbacks.Common.CompilerDeadMetadata
import Itasca.Runtime.Code.Local.Relations.Common.StatefulEmissionTransport
import Itasca.Runtime.Code.Body.Reader.Common.ReaderBoundary
import Itasca.Runtime.Code.Body.Reader.Control.ReaderScopeFronts
import Itasca.Runtime.Code.Body.Reader.Common.ReaderReachabilitySteps
import Itasca.Runtime.Code.Body.Reader.Common.ReaderKnownFronts
import Itasca.Runtime.Code.Body.Reader.Common.ReaderPostDeclared
import Itasca.Runtime.Code.Local.Callbacks.Calls.CallbackIndirect
import Itasca.Runtime.Code.Body.Reader.Common.ReaderEnterWasm2
import Itasca.Runtime.Code.Body.Reader.Control.ReaderBranchWasm2
import Itasca.Runtime.Code.Body.Reader.Common.ReaderCloseWasm2
import Itasca.Runtime.Code.Body.Reader.Control.ReaderCompilerScopes
import Itasca.Runtime.Code.Body.Reader.Control.ReaderControlBoundary
import Itasca.Runtime.Code.Local.Callbacks.Common.FramePlanPop
import Itasca.Runtime.Code.Local.Callbacks.Control.ElseSource
import Itasca.Runtime.Code.Local.Callbacks.Control.ElseFrames
import Itasca.Runtime.Code.Local.Callbacks.Calls.ScopeCallbackEnter
import Itasca.Runtime.Code.Local.Relations.Control.ControlEntrySuccess
import Itasca.Runtime.Code.Local.Callbacks.Common.CompilerEnterMetadata
import Itasca.Runtime.Code.Local.Relations.Control.ControlCursor
import Itasca.Runtime.Code.Local.Relations.Control.ControlSources
import Itasca.Runtime.Code.Local.Relations.Control.ControlObservedLayout
import Itasca.Runtime.Code.Body.Callbacks.Calls.ScopeCallbackInputs
import Itasca.Runtime.Code.Body.Reader.Common.ReaderReachability
import Itasca.Runtime.Code.Body.Reader.Common.ReaderFrontTransitions
import Itasca.Runtime.Code.Local.Callbacks.Calls.ScopeCallbackDead
import Itasca.Runtime.Code.Local.Relations.Common.KnownPopStack
import Itasca.Runtime.Code.Body.Reader.Common.ReaderKnownFrontEntry
import Itasca.Runtime.Code.Local.Callbacks.Calls.ScopeCallbackIf
import Itasca.Runtime.Code.Local.Callbacks.Control.ScopeFrameSelect
import Itasca.Runtime.Code.Body.Reader.Control.ReaderBranchEffects
import Itasca.Runtime.Code.Body.Reader.Control.ReaderBranchLayout
import Itasca.Runtime.Code.Local.Callbacks.Common.FramePlanUpdate
import Itasca.Runtime.Code.Local.Relations.Control.ResolvedBranchPrefix
import Itasca.Runtime.Code.Local.Control.Control.UniversalBranch
import Itasca.Runtime.Code.Local.Relations.Common.ResolvedConditionalPrefix
import Itasca.Runtime.Code.Local.Control.Common.UniversalConditional
import Itasca.Runtime.Code.Local.Callbacks.Control.ElseEvidence
import Itasca.Runtime.Code.Local.Relations.Calls.BranchSuccessCallbacks
import Itasca.Runtime.Code.Local.Relations.Control.BranchSuccessControls
import Itasca.Runtime.Code.Local.Callbacks.Calls.CompilerCallbackMetadata
import Itasca.Runtime.Code.Local.Callbacks.Calls.CallbackSources
import Itasca.Runtime.Code.Local.Callbacks.Calls.CallbackCursor
import Itasca.Runtime.Code.Body.Reader.Common.ReaderWasm2
import Itasca.Runtime.Code.Local.Source.SourceStacks
import Itasca.Runtime.Code.Body.Reader.Common.ReaderSpan
import Itasca.Runtime.Code.Body.Relations.Control.BranchIfLayout
import Itasca.Runtime.Code.Local.Relations.Control.BranchReachable
import Itasca.Runtime.Code.Local.Relations.Calls.BranchSuccessConditionalCallbacks
import Itasca.Runtime.Code.Body.Reader.Control.ReaderBranchIfLayout
import Itasca.Runtime.Code.Local.Callbacks.Control.ElseTransition
import Itasca.Runtime.Code.Local.Relations.Common.ResolvedGuards
import Itasca.Runtime.Code.Local.Callbacks.Control.ScopeStackElse
import Itasca.Runtime.Code.Local.Callbacks.Control.ScopeStackClose
import Itasca.Runtime.Code.Local.Callbacks.Control.EnterElse
import Itasca.Runtime.Code.Local.Callbacks.Common.CompilerCloseMetadata
import Itasca.Runtime.Code.Local.Relations.Control.ControlMapCounts
import Itasca.Runtime.Code.Local.Relations.Control.KnownControlStack
import Itasca.Runtime.Code.Local.Callbacks.Control.ElseSuccess
import Itasca.Runtime.Code.Local.Control.Common.UniversalRoot
import Itasca.Runtime.Code.Local.Callbacks.Control.CloseGuardedScope
import Itasca.Runtime.Code.Local.Relations.Common.ResolvedLiteral
import Itasca.Runtime.Code.Body.Reader.Common.ReaderEndSignature
import Itasca.Runtime.Code.Local.Callbacks.Common.CloseFunction
import Itasca.Runtime.Code.Local.Relations.Common.Function
import Itasca.Runtime.Code.Local.Relations.Common.LabelWiden
import Itasca.Runtime.Code.Local.Source.TypedRunClosed
import Itasca.Runtime.Code.Body.Reader.Common.ReaderStacks
namespace Itasca.Runtime.Code
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

end Itasca.Runtime.Code
