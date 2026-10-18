import Exec.Code.Module.CompileSourceCertificate
import Exec.Code.Module.CompileDriverFrame
import Exec.Code.Module.SchedulerFunctions
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem sourceFunctions_length {raw : ModuleBinary.Module}
    (count : raw.functions.length = raw.codes.length) :
    (sourceFunctions raw).length = raw.functions.length := by
  simp [sourceFunctions, List.length_zipWith, count]

/-- Actual environment preparation initializes the canonical source-indexed
certificate ledger with every defined function still uncompiled. -/
theorem CompileSourceCertificate.initial_functions {A : Type} {ops : runtime.platform.Alloc A}
    {bytes profile limits executable} {w : CompileWitness ops bytes profile limits executable}
    (c : CompileSourceCertificate w) (law : Platform.AllocCorrect ops) :
    PartialModuleFunctions w.env (sourceFunctions c.raw) c.run.remaining.configured.functions.val := by
  have prepared := compiler_driver_configured ops law c.run
    (by simp [initialScheduler, alloc.vec.Vec.new])
    (by simp [initialScheduler, alloc.vec.Vec.new])
    (by simp [initialScheduler, alloc.vec.Vec.new])
  rw [prepared.2.2.1]
  apply PartialModuleFunctions.empty
  rw [sourceFunctions_length (by rw [c.functions, c.codeCount]), c.functions]

/-- Once actual submission has filled the canonical ledger, the remaining
driver phases, collection and initializer lowering establish module coverage.
No further compiler relation or callback premise is required. -/
theorem CompileSourceCertificate.functions_of_submission {A : Type} {ops : runtime.platform.Alloc A}
    {bytes profile limits executable} {w : CompileWitness ops bytes profile limits executable}
    (c : CompileSourceCertificate w) (law : Platform.AllocCorrect ops)
    (ledger : PartialModuleFunctions w.env (sourceFunctions c.raw) c.run.remaining.submitted.functions.val) :
    ModuleFunctions executable (sourceFunctions c.raw) ∧ InitializerMappings executable := by
  have after := compiler_driver_after_submission ops c.run.remaining
  have functions := congrArg runtime.compiler.CompileScheduler.functions after
  have final : PartialModuleFunctions w.env (sourceFunctions c.raw) w.scheduler.functions.val := by
    simpa only [functions] using ledger
  exact w.defined_functions law (final.complete w.functions.val (w.function_order law))
end Exec.Code
