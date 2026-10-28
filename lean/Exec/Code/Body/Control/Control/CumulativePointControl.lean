import Exec.Code.Body.Callbacks.Common.CompilerPrefix
import Exec.Code.Local.Control.Common.Structured
import Exec.Code.Local.Control.Common.StructuredComposition
import Exec.Code.Local.Relations.Common.Concatenation
import Exec.Code.Local.Relations.Common.Extension
import Exec.Code.Local.Relations.Common.PrefixZipper
import Exec.Code.Local.Relations.Common.Prefix
import Exec.Code.Local.Relations.Common.ResolvedPrefix
import Exec.Code.Local.Control.Common.UniversalPrefix
import Exec.Code.Local.Control.Common.UniversalTerminal
import Exec.Code.Local.Control.Common.UniversalDormant
import Exec.Code.Local.Callbacks.Common.CompilerDeadMetadata
import Exec.Code.Local.Relations.Common.StatefulEmissionTransport
import Exec.Code.Body.Reader.Common.ReaderBoundary
import Exec.Code.Body.Reader.Control.ReaderScopeFronts
import Exec.Code.Body.Reader.Common.ReaderReachabilitySteps
import Exec.Code.Body.Reader.Common.ReaderKnownFronts
import Exec.Code.Body.Reader.Common.ReaderPostDeclared
import Exec.Code.Local.Callbacks.Calls.CallbackIndirect
import Exec.Code.Body.Reader.Common.ReaderEnterWasm2
import Exec.Code.Body.Reader.Control.ReaderBranchWasm2
import Exec.Code.Body.Reader.Common.ReaderCloseWasm2
import Exec.Code.Body.Reader.Control.ReaderCompilerScopes
import Exec.Code.Body.Reader.Control.ReaderControlBoundary
import Exec.Code.Local.Callbacks.Common.FramePlanPop
import Exec.Code.Local.Callbacks.Control.ElseSource
import Exec.Code.Local.Callbacks.Control.ElseFrames
import Exec.Code.Local.Callbacks.Calls.ScopeCallbackEnter
import Exec.Code.Local.Relations.Control.ControlEntrySuccess
import Exec.Code.Local.Callbacks.Common.CompilerEnterMetadata
import Exec.Code.Local.Relations.Control.ControlCursor
import Exec.Code.Local.Relations.Control.ControlSources
import Exec.Code.Local.Relations.Control.ControlObservedLayout
import Exec.Code.Body.Callbacks.Calls.ScopeCallbackInputs
import Exec.Code.Body.Reader.Common.ReaderReachability
import Exec.Code.Body.Reader.Common.ReaderFrontTransitions
import Exec.Code.Local.Callbacks.Calls.ScopeCallbackDead
import Exec.Code.Local.Relations.Common.KnownPopStack
import Exec.Code.Body.Reader.Common.ReaderKnownFrontEntry
import Exec.Code.Local.Callbacks.Calls.ScopeCallbackIf
import Exec.Code.Local.Callbacks.Control.ScopeFrameSelect
import Exec.Code.Body.Reader.Control.ReaderBranchEffects
import Exec.Code.Body.Reader.Control.ReaderBranchLayout
import Exec.Code.Local.Callbacks.Common.FramePlanUpdate
import Exec.Code.Local.Relations.Control.ResolvedBranchPrefix
import Exec.Code.Local.Control.Control.UniversalBranch
import Exec.Code.Local.Relations.Common.ResolvedConditionalPrefix
import Exec.Code.Local.Control.Common.UniversalConditional
import Exec.Code.Local.Callbacks.Control.ElseEvidence
import Exec.Code.Local.Relations.Calls.BranchSuccessCallbacks
import Exec.Code.Local.Relations.Control.BranchSuccessControls
import Exec.Code.Local.Callbacks.Calls.CompilerCallbackMetadata
import Exec.Code.Local.Callbacks.Calls.CallbackSources
import Exec.Code.Local.Callbacks.Calls.CallbackCursor
import Exec.Code.Body.Reader.Common.ReaderWasm2
import Exec.Code.Local.Source.SourceStacks
import Exec.Code.Body.Reader.Common.ReaderSpan
import Exec.Code.Body.Relations.Control.BranchIfLayout
import Exec.Code.Local.Relations.Control.BranchReachable
import Exec.Code.Local.Relations.Calls.BranchSuccessConditionalCallbacks
import Exec.Code.Body.Reader.Control.ReaderBranchIfLayout
import Exec.Code.Local.Callbacks.Control.ElseTransition
import Exec.Code.Local.Relations.Common.ResolvedGuards
import Exec.Code.Local.Callbacks.Control.ScopeStackElse
import Exec.Code.Local.Callbacks.Control.ScopeStackClose
import Exec.Code.Local.Callbacks.Control.EnterElse
import Exec.Code.Local.Callbacks.Common.CompilerCloseMetadata
import Exec.Code.Local.Relations.Control.ControlMapCounts
import Exec.Code.Local.Relations.Control.KnownControlStack
import Exec.Code.Local.Callbacks.Control.ElseSuccess
import Exec.Code.Local.Control.Common.UniversalRoot
import Exec.Code.Local.Callbacks.Control.CloseGuardedScope
import Exec.Code.Local.Relations.Common.ResolvedLiteral
import Exec.Code.Body.Reader.Common.ReaderEndSignature
import Exec.Code.Local.Callbacks.Common.CloseFunction
import Exec.Code.Local.Relations.Common.Function
import Exec.Code.Local.Relations.Common.LabelWiden
import Exec.Code.Local.Source.TypedRunClosed
import Exec.Code.Body.Reader.Common.ReaderStacks
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
