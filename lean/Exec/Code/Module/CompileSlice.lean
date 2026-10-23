import Exec.Code.Module.CompileSourceSetup
import Exec.Code.Module.CompileSchedulerAssembly
import Exec.Code.Module.SchedulerSubmission
import Exec.Code.Local.Source.SourceBatchLookup
import Exec.Code.Body.Relations.Common.EntryCompilerInitial
import Exec.Code.Body.Callbacks.Common.CompilerPrefix
import Exec.Code.Body.Reader.Common.ReaderBoundary
import Exec.Code.Body.Reader.Control.ReaderScopeFronts
import Exec.Code.Body.Reader.Common.ReaderReachabilitySteps
import Exec.Code.Local.Control.Common.UniversalTerminal
import Exec.Code.Local.Relations.Common.Prefix
import Exec.Code.Local.Callbacks.Common.CompilerDeadMetadata
import Exec.Code.Local.Control.Common.UniversalRoot
import Exec.Code.Local.Callbacks.Common.CompilerCloseMetadata
import Exec.Code.Body.Reader.Control.ReaderControlBoundary
import Exec.Code.Local.Source.TypedRunClosed
import Exec.Code.Body.Reader.Common.ReaderStacks
import Exec.Code.Local.Callbacks.Common.CompilerMetadata
import Exec.Code.Local.Callbacks.Common.CloseFunction
import Exec.Code.Local.Relations.Common.Function
import Exec.Code.Local.Relations.Common.LabelWiden
import Exec.Code.Local.Relations.Common.Extension
import Itasca.Support.EnvTranslation
import Exec.Code.Body.Reader.Common.ReaderCompilerOrdinary
import Exec.Code.Body.Reader.Control.ReaderCompilerScopes
import Exec.Code.Body.Reader.Common.ReaderCompilerBounds
import Exec.Code.Local.Callbacks.Control.ElseSource
import Exec.Code.Local.Callbacks.Control.ElseTransition
import Exec.Code.Local.Callbacks.Common.FramePlanPop
import Exec.Code.Local.Relations.Common.ResolvedGuards
import Exec.Code.Local.Callbacks.Control.ScopeStackElse
import Exec.Code.Local.Control.Common.UniversalDormant
import Exec.Code.Local.Callbacks.Control.ScopeStackClose
import Exec.Code.Local.Callbacks.Control.EnterElse
import Exec.Code.Local.Relations.Control.ControlCursor
import Exec.Code.Local.Relations.Control.ControlSources
import Exec.Code.Local.Relations.Control.ControlMapCounts
import Exec.Code.Local.Relations.Control.KnownControlStack
import Exec.Code.Local.Callbacks.Control.ElseSuccess
import Exec.Code.Local.Relations.Control.ControlObservedLayout
import Exec.Code.Local.Relations.Common.PrefixZipper
import Exec.Code.Local.Callbacks.Control.ElseFrames
import Exec.Code.Local.Callbacks.Control.CloseGuardedScope
import Exec.Code.Local.Relations.Common.ResolvedLiteral
import Exec.Code.Body.Reader.Common.ReaderEndSignature
import Exec.Code.Module.CompileEntryBounds
import Exec.Code.Local.Source.SourceSubmission

/-! Source-ordered slice certificates from the actual compiler driver.
Shared setup fixes reader coordinates; this module discharges its own submission fold. -/
namespace Exec.Code
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

end Exec.Code
