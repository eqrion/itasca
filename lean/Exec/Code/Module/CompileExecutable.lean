import Exec.Code.Module.CompileSourceSetup
import Exec.Code.Module.ExecutableCompileSchedulerAssembly
import Exec.Code.Module.SchedulerExecutable
import Exec.Code.Module.CompileSlice

/-! Source-ordered executable certificates from the actual compiler driver.
Shared setup fixes reader coordinates; this module discharges its own submission fold. -/
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca
theorem CompileSourceCertificate.executable_functions {A : Type} {ops : runtime.platform.Alloc A}
    {bytes profile limits executable} {w : CompileWitness ops bytes profile limits executable}
    (c : CompileSourceCertificate w) (law : Platform.AllocCorrect ops) :
    ExecutableModuleFunctions executable (sourceFunctions c.raw) ∧ InitializerMappings executable := by
  obtain ⟨signatures,slots,origin⟩ := c.scheduler_setup law
  have initial : SchedulerExecutable w.env (sourceFunctions c.raw) c.run.remaining.configured :=
    ⟨signatures, slots, origin, c.initial_executable_functions law⟩
  have submitted := c.run.remaining.submit_call
  rw [c.code_length] at submitted
  have certified := compiler_submit_source_executable_functions ops law
    runtime.compiler.CompileSource.Insts.ItascaStreamSource
    {bytes, code_start := w.codeStart, code_end := w.codeEnd} 0#u64
    w.env c.code profile c.run.remaining.config c.raw c.functions c.entryBounds
    c.environmentProfile.1 c.environment.val c.tail.val c.available c.codeBound
    c.run.remaining.entries c.entries c.codeCount c.run.remaining.configured c.run.remaining.submitted
    c.run.remaining.pending initial submitted
  exact c.executable_functions_of_submission law certified.functions

/-- Public successful compilation produces
source-ordered certificates for the exact canonical module syntax. -/
theorem compile_executable_functions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bytes : Slice U8) (profile : ValidationProfile)
    (limits : runtime.compiler.CompileLimits) (executable : runtime.compiler.ExecutableModule)
    (accepted : runtime.compiler.compile_with ops bytes profile limits = .ok (.Ok executable)) :
    ∃ raw, ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile ∧
      ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw) ∧
      ModuleElaboration.Matches executable.module.env executable.module.tail raw ∧
      Module_ok (ModuleElaboration.moduleOf raw) ∧ ModuleElaboration.Profile raw profile ∧
      ModuleElaboration.AccessorTypes executable.module.env raw ∧
      ExecutableModuleFunctions executable (sourceFunctions raw) ∧ InitializerMappings executable ∧
      executable.profile = profile := by
  obtain ⟨w⟩ := compile_accepted ops bytes profile limits executable accepted
  obtain ⟨c⟩ := w.source_certificate law
  have certificates := c.executable_functions law
  obtain ⟨raw, encoded, elaborated, matched, typed, restrictions, accessors⟩ := (w.source_validated law).1
  have same := Profile.module_unique encoded c.encoded
  subst raw
  exact ⟨c.raw, c.encoded, elaborated, matched, typed, restrictions, accessors,
    certificates.1, certificates.2, (w.initializers law).2.1⟩
end Itasca.Runtime.Code
