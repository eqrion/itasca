import Exec.Code.Module.CompileSourceSetup
import Exec.Code.Module.CompileSchedulerAssembly
import Exec.Code.Module.SchedulerSlice

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

/-- Actual successful compilation establishes all defined-function source
certificates for the independently encoded integer slice. The scheduler,
reader, compiler callbacks and final assembly are discharged internally. -/
theorem CompileSourceCertificate.slice_functions {A : Type} {ops : runtime.platform.Alloc A}
    {bytes profile limits executable} {w : CompileWitness ops bytes profile limits executable}
    (c : CompileSourceCertificate w) (law : Platform.AllocCorrect ops) (subset : ModuleSlice c.raw) :
    ModuleFunctions executable (sourceFunctions c.raw) ∧ InitializerMappings executable := by
  obtain ⟨signatures,slots,origin⟩ := c.scheduler_setup law
  have initial : SchedulerSlice w.env (sourceFunctions c.raw) c.run.remaining.configured :=
    ⟨signatures, slots, origin, c.initial_functions law⟩
  have submitted := c.run.remaining.submit_call
  rw [c.code_length] at submitted
  have certified := compiler_submit_source_functions ops law
    runtime.compiler.CompileSource.Insts.ItascaStreamSource
    {bytes, code_start := w.codeStart, code_end := w.codeEnd} 0#u64
    w.env c.code profile c.run.remaining.config c.raw subset c.functions c.entryBounds
    c.environmentProfile.1 c.environment.val c.tail.val c.available c.codeBound
    c.run.remaining.entries c.entries c.codeCount c.run.remaining.configured c.run.remaining.submitted
    c.run.remaining.pending initial submitted
  exact c.functions_of_submission law certified.functions

/-- Public compilation of an independently encoded slice module produces
source-ordered certificates for the exact canonical module syntax. -/
theorem compile_slice_functions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bytes : Slice U8) (profile : ValidationProfile)
    (limits : runtime.compiler.CompileLimits) (executable : runtime.compiler.ExecutableModule)
    (subset : SourceSlice profile bytes)
    (accepted : runtime.compiler.compile_with ops bytes profile limits = .ok (.Ok executable)) :
    ∃ raw, ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile ∧
      ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw) ∧
      ModuleElaboration.Matches executable.module.env executable.module.tail raw ∧
      Module_ok (ModuleElaboration.moduleOf raw) ∧ ModuleElaboration.Profile raw profile ∧
      ModuleElaboration.AccessorTypes executable.module.env raw ∧ ModuleSlice raw ∧
      ModuleFunctions executable (sourceFunctions raw) ∧ InitializerMappings executable ∧
      executable.profile = profile := by
  obtain ⟨w⟩ := compile_accepted ops bytes profile limits executable accepted
  obtain ⟨c⟩ := w.source_certificate law
  have certificates := c.slice_functions law (subset.decoded c.encoded)
  obtain ⟨raw, encoded, elaborated, matched, typed, restrictions, accessors⟩ := (w.source_validated law).1
  have same := Profile.module_unique encoded c.encoded
  subst raw
  exact ⟨c.raw, c.encoded, elaborated, matched, typed, restrictions, accessors,
    subset.decoded c.encoded, certificates.1, certificates.2, (w.initializers law).2.1⟩
end Exec.Code
