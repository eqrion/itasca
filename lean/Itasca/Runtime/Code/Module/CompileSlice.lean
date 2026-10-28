import Itasca.Runtime.Code.Module.CompileSourceSetup
import Itasca.Runtime.Code.Module.CompileSchedulerAssembly
import Itasca.Runtime.Code.Module.SchedulerSubmission
import Itasca.Runtime.Code.Local.Source.SourceBatchLookup
import Itasca.Runtime.Code.Body.Relations.Common.EntryCompilerInitial
import Itasca.Runtime.Code.Body.Callbacks.Common.CompilerPrefix
import Itasca.Runtime.Code.Body.Reader.Common.ReaderBoundary
import Itasca.Runtime.Code.Body.Reader.Control.ReaderScopeFronts
import Itasca.Runtime.Code.Body.Reader.Common.ReaderReachabilitySteps
import Itasca.Runtime.Code.Local.Control.Common.UniversalTerminal
import Itasca.Runtime.Code.Local.Relations.Common.Prefix
import Itasca.Runtime.Code.Local.Callbacks.Common.CompilerDeadMetadata
import Itasca.Runtime.Code.Local.Control.Common.UniversalRoot
import Itasca.Runtime.Code.Local.Callbacks.Common.CompilerCloseMetadata
import Itasca.Runtime.Code.Body.Reader.Control.ReaderControlBoundary
import Itasca.Runtime.Code.Local.Source.TypedRunClosed
import Itasca.Runtime.Code.Body.Reader.Common.ReaderStacks
import Itasca.Runtime.Code.Local.Callbacks.Common.CompilerMetadata
import Itasca.Runtime.Code.Local.Callbacks.Common.CloseFunction
import Itasca.Runtime.Code.Local.Relations.Common.Function
import Itasca.Runtime.Code.Local.Relations.Common.LabelWiden
import Itasca.Runtime.Code.Local.Relations.Common.Extension
import Itasca.Support.EnvTranslation
import Itasca.Runtime.Code.Body.Reader.Common.ReaderCompilerOrdinary
import Itasca.Runtime.Code.Body.Reader.Control.ReaderCompilerScopes
import Itasca.Runtime.Code.Body.Reader.Common.ReaderCompilerBounds
import Itasca.Runtime.Code.Local.Callbacks.Control.ElseSource
import Itasca.Runtime.Code.Local.Callbacks.Control.ElseTransition
import Itasca.Runtime.Code.Local.Callbacks.Common.FramePlanPop
import Itasca.Runtime.Code.Local.Relations.Common.ResolvedGuards
import Itasca.Runtime.Code.Local.Callbacks.Control.ScopeStackElse
import Itasca.Runtime.Code.Local.Control.Common.UniversalDormant
import Itasca.Runtime.Code.Local.Callbacks.Control.ScopeStackClose
import Itasca.Runtime.Code.Local.Callbacks.Control.EnterElse
import Itasca.Runtime.Code.Local.Relations.Control.ControlCursor
import Itasca.Runtime.Code.Local.Relations.Control.ControlSources
import Itasca.Runtime.Code.Local.Relations.Control.ControlMapCounts
import Itasca.Runtime.Code.Local.Relations.Control.KnownControlStack
import Itasca.Runtime.Code.Local.Callbacks.Control.ElseSuccess
import Itasca.Runtime.Code.Local.Relations.Control.ControlObservedLayout
import Itasca.Runtime.Code.Local.Relations.Common.PrefixZipper
import Itasca.Runtime.Code.Local.Callbacks.Control.ElseFrames
import Itasca.Runtime.Code.Local.Callbacks.Control.CloseGuardedScope
import Itasca.Runtime.Code.Local.Relations.Common.ResolvedLiteral
import Itasca.Runtime.Code.Body.Reader.Common.ReaderEndSignature
import Itasca.Runtime.Code.Module.CompileEntryBounds
import Itasca.Runtime.Code.Local.Source.SourceSubmission

/-! Source-ordered slice certificates from the actual compiler driver.
Shared setup fixes reader coordinates; this module discharges its own submission fold. -/
namespace Itasca.Runtime.Code
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

end Itasca.Runtime.Code
