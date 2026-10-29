import Itasca.Runtime.Compiler.Module.CompileSourceSetup
import Itasca.Runtime.Compiler.Module.CompileSchedulerAssembly
import Itasca.Runtime.Compiler.Module.SchedulerSubmission
import Itasca.Runtime.Compiler.Local.Source.SourceBatchLookup
import Itasca.Runtime.Compiler.Body.Relations.Entry.EntryCompilerInitial
import Itasca.Runtime.Compiler.Body.Callbacks.Prefix.CompilerPrefix
import Itasca.Runtime.Compiler.Body.Reader.Control.Boundary
import Itasca.Runtime.Compiler.Body.Reader.Control.ScopeFronts
import Itasca.Runtime.Compiler.Body.Reader.Control.ReachabilitySteps
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalTerminal
import Itasca.Runtime.Compiler.Local.Relations.Prefix.Prefix
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerDeadMetadata
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalRoot
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerCloseMetadata
import Itasca.Runtime.Compiler.Body.Reader.Control.ControlBoundary
import Itasca.Runtime.Compiler.Local.Source.TypedRunClosed
import Itasca.Runtime.Compiler.Body.Reader.Stacks.Stacks
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerMetadata
import Itasca.Runtime.Compiler.Local.Callbacks.Function.CloseFunction
import Itasca.Runtime.Compiler.Local.Relations.Function.Function
import Itasca.Runtime.Compiler.Local.Relations.Prefix.LabelWiden
import Itasca.Runtime.Compiler.Local.Relations.Prefix.Extension
import Itasca.Support.EnvTranslation
import Itasca.Runtime.Compiler.Local.Relations.Syntax.ReaderOpcode
import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericEncoding
import Itasca.Runtime.Compiler.Body.Reader.Scalar.SignEmissions
import Itasca.Runtime.Compiler.Body.Reader.Replay.Span
import Itasca.Runtime.Compiler.Local.Source.SourceCursor
import Itasca.Runtime.Compiler.Local.Relations.Operations.DeadCode
import Itasca.Runtime.Compiler.Body.Reader.Replay.ProfileAgreement
import Itasca.Runtime.Compiler.Local.Relations.Stacks.KnownPopStack
import Itasca.Runtime.Compiler.Local.Relations.Stacks.KnownNumericStack
import Itasca.Runtime.Compiler.Body.Reader.Scalar.SignExtension
import Itasca.Runtime.Compiler.Body.Reader.Scalar.NumericEmissions
import Itasca.Runtime.Compiler.Body.Reader.Scalar.IntegerFacts
import Itasca.Runtime.Compiler.Body.Reader.Scalar.Emissions
import Itasca.Runtime.Compiler.Body.Reader.Scalar.Empty
import Itasca.Runtime.Compiler.Local.Lowering.Literal.LiteralSources
import Itasca.Runtime.Compiler.Local.Source.SourceLengthsTactic
import Itasca.Runtime.Compiler.Local.Lowering.Integer.LoweringArithmetic
import Itasca.Runtime.Compiler.Local.Lowering.Local.LoweringLocal
import Itasca.Runtime.Compiler.Local.Lowering.Literal.LiteralCursor
import Itasca.Runtime.Compiler.Local.Source.SourceCursorTactic
import Itasca.Runtime.Compiler.Body.Source.TypedLowering
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerLiteralMetadata
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerMetadataTactic
import Itasca.Runtime.Compiler.Body.Reader.Local.LocalEmissions
import Itasca.Runtime.Compiler.Body.Reader.Local.LocalEffects
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalPrefix
import Itasca.Runtime.Compiler.Body.Reader.Calls.CallLowering
import Itasca.Runtime.Compiler.Body.Reader.Calls.CallEffects
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackSources
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackCursor
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerOrdinaryResults
import Itasca.Runtime.Compiler.Local.Capacity.EmissionGrowth
import Itasca.Runtime.Compiler.Body.Reader.Scalar.Unreachable
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Local.Lowering.Control.LoweringReturn
import Itasca.Runtime.Compiler.Local.Relations.Control.KnownControlStack
import Itasca.Runtime.Compiler.Body.Reader.Control.ReturnStack
import Itasca.Runtime.Compiler.Body.Reader.Control.RootFrame
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
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalDormant
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.ScopeCallbackDead
import Itasca.Runtime.Compiler.Body.Reader.Control.EnterWasm2
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.ScopeCallbackIf
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchLayout
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalConditional
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseEvidence
import Itasca.Runtime.Compiler.Local.Relations.Calls.BranchSuccessCallbacks
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchSuccessControls
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CompilerCallbackMetadata
import Itasca.Runtime.Compiler.Body.Reader.Replay.Post
import Itasca.Runtime.Compiler.Local.Source.SourceStacks
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchWasm2
import Itasca.Runtime.Compiler.Body.Relations.Control.BranchIfLayout
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchReachable
import Itasca.Runtime.Compiler.Local.Relations.Calls.BranchSuccessConditionalCallbacks
import Itasca.Runtime.Compiler.Body.Reader.Replay.CompilerBounds
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseSource
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseTransition
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ResolvedGuards
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ScopeStackElse
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ScopeStackClose
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EnterElse
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlMapCounts
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseSuccess
import Itasca.Runtime.Compiler.Local.Relations.Prefix.PrefixZipper
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CloseGuardedScope
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ResolvedLiteral
import Itasca.Runtime.Compiler.Body.Reader.Control.EndSignature
import Itasca.Runtime.Compiler.Module.CompileEntry
import Itasca.Runtime.Compiler.Local.Source.SourceSubmission

/-! Source-ordered slice certificates from the actual compiler driver.
Shared setup fixes reader coordinates; this module discharges its own submission fold. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- The actual concrete source supplies every exact read used by the retained
canonical code-section certificate. -/
theorem CompileSourceCertificate.available {A : Type} {ops : runtime.platform.Alloc A}
    {bytes profile limits executable} {w : CompileWitness ops bytes profile limits executable}
    (c : CompileSourceCertificate w) :
    StreamSource.Available runtime.compiler.CompileSource.Insts.ItascaStreamSource
      {bytes, code_start := w.codeStart, code_end := w.codeEnd} c.environment.val c.code.val c.tail.val := by
  have bounds := code_region_spec bytes
  rw [w.region, WP.spec_ok] at bounds
  let source : runtime.compiler.CompileSource := {bytes, code_start := w.codeStart, code_end := w.codeEnd}
  have actual := source_available source bounds
  obtain ⟨len, readLen, length⟩ := actual.code_len_read
  have codeLength := c.coherent.code_len_eq len readLen
  constructor
  · obtain ⟨buffer, read, _⟩ := actual.environment_read
    exact ⟨buffer, read, c.coherent.environment_eq buffer read⟩
  · exact ⟨len, readLen, codeLength⟩
  · intro first last order bound
    obtain ⟨buffer, read, _⟩ := actual.code_read first last order (by omega)
    exact ⟨buffer, read, c.coherent.code_eq first last buffer order bound read⟩
  · obtain ⟨buffer, read, _⟩ := actual.tail_read
    exact ⟨buffer, read, c.coherent.tail_eq buffer read⟩

end Itasca.Runtime.Compiler
