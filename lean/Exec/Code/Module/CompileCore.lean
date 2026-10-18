import Exec.Code.Module.CoreCompileSchedulerAssembly
import Exec.Code.Module.SchedulerCore
import Exec.Code.Module.CompileSlice
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
theorem CompileSourceCertificate.core_functions {A : Type} {ops : runtime.platform.Alloc A}
    {bytes profile limits executable} {w : CompileWitness ops bytes profile limits executable}
    (c : CompileSourceCertificate w) (law : Platform.AllocCorrect ops) (subset : ModuleCore c.raw) :
    CoreModuleFunctions executable (sourceFunctions c.raw) ∧ InitializerMappings executable := by
  have prepared := compiler_driver_configured ops law c.run
    (by simp [initialScheduler, alloc.vec.Vec.new])
    (by simp [initialScheduler, alloc.vec.Vec.new])
    (by simp [initialScheduler, alloc.vec.Vec.new])
  have bounds := code_region_spec bytes
  rw [w.region, WP.spec_ok] at bounds
  have origin : c.run.remaining.configured.code_start.val ≤ Itasca.limits.MAX_MODULE_BYTES.val := by
    rw [prepared.2.2.2]
    change w.codeStart.val ≤ _
    exact bounds.1.trans (bounds.2.trans c.moduleBound)
  have initial : SchedulerCore w.env (sourceFunctions c.raw) c.run.remaining.configured :=
    ⟨prepared.1, prepared.2.1, origin, c.initial_core_functions law⟩
  have length : c.run.remaining.codeLength = Slice.len c.code := by
    apply UScalar.eq_of_val_eq
    exact c.coherent.code_len_eq _ c.run.remaining.length_call
  have submitted := c.run.remaining.submit_call
  rw [length] at submitted
  have certified := compiler_submit_source_core_functions ops law
    runtime.compiler.CompileSource.Insts.ItascaStreamSource
    {bytes, code_start := w.codeStart, code_end := w.codeEnd} 0#u64
    w.env c.code profile c.run.remaining.config c.raw subset c.functions c.entryBounds
    c.environmentProfile.1 c.environment.val c.tail.val c.available c.codeBound
    c.run.remaining.entries c.entries c.codeCount c.run.remaining.configured c.run.remaining.submitted
    c.run.remaining.pending initial submitted
  exact c.core_functions_of_submission law certified.functions

/-- Public compilation of an independently encoded core module produces
source-ordered certificates for the exact canonical module syntax. -/
theorem compile_core_functions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bytes : Slice U8) (profile : ValidationProfile)
    (limits : runtime.compiler.CompileLimits) (executable : runtime.compiler.ExecutableModule)
    (subset : SourceCore profile bytes)
    (accepted : runtime.compiler.compile_with ops bytes profile limits = .ok (.Ok executable)) :
    ∃ raw, ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile ∧
      ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw) ∧
      ModuleElaboration.Matches executable.module.env executable.module.tail raw ∧
      Module_ok (ModuleElaboration.moduleOf raw) ∧ ModuleElaboration.Profile raw profile ∧
      ModuleElaboration.AccessorTypes executable.module.env raw ∧ ModuleCore raw ∧
      CoreModuleFunctions executable (sourceFunctions raw) ∧ InitializerMappings executable ∧
      executable.profile = profile := by
  obtain ⟨w⟩ := compile_accepted ops bytes profile limits executable accepted
  obtain ⟨c⟩ := w.source_certificate law
  have certificates := c.core_functions law (subset.decoded c.encoded)
  obtain ⟨raw, encoded, elaborated, matched, typed, restrictions, accessors⟩ := (w.source_validated law).1
  have same := Profile.module_unique encoded c.encoded
  subst raw
  exact ⟨c.raw, c.encoded, elaborated, matched, typed, restrictions, accessors,
    subset.decoded c.encoded, certificates.1, certificates.2, (w.initializers law).2.1⟩
end Exec.Code
