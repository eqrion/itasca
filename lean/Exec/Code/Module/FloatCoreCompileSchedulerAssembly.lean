import Exec.Code.Module.CompileSourceCertificate
import Exec.Code.Module.CompileDriverFrame
import Exec.Code.Module.FloatCoreSchedulerFunctions
import Exec.Code.Module.CompileSchedulerAssembly
import Exec.Code.Module.FloatCoreCompileAssembly
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
theorem CompileSourceCertificate.initial_float_core_functions {A : Type} {ops : runtime.platform.Alloc A}
    {bytes profile limits executable} {w : CompileWitness ops bytes profile limits executable}
    (c : CompileSourceCertificate w) (law : Platform.AllocCorrect ops) :
    PartialFloatCoreModuleFunctions w.env (sourceFunctions c.raw) c.run.remaining.configured.functions.val := by
  have prepared := compiler_driver_configured ops law c.run
    (by simp [initialScheduler, alloc.vec.Vec.new])
    (by simp [initialScheduler, alloc.vec.Vec.new])
    (by simp [initialScheduler, alloc.vec.Vec.new])
  rw [prepared.2.2.1]
  apply PartialFloatCoreModuleFunctions.empty
  rw [sourceFunctions_length (by rw [c.functions, c.codeCount]), c.functions]

/-- Once actual submission has filled the canonical ledger, the remaining
driver phases, collection and initializer lowering establish module coverage.
No further compiler relation or callback premise is required. -/
theorem CompileSourceCertificate.float_core_functions_of_submission {A : Type} {ops : runtime.platform.Alloc A}
    {bytes profile limits executable} {w : CompileWitness ops bytes profile limits executable}
    (c : CompileSourceCertificate w) (law : Platform.AllocCorrect ops)
    (ledger : PartialFloatCoreModuleFunctions w.env (sourceFunctions c.raw) c.run.remaining.submitted.functions.val) :
    FloatCoreModuleFunctions executable (sourceFunctions c.raw) ∧ InitializerMappings executable := by
  have after := compiler_driver_after_submission ops c.run.remaining
  have functions := congrArg runtime.compiler.CompileScheduler.functions after
  have final : PartialFloatCoreModuleFunctions w.env (sourceFunctions c.raw) w.scheduler.functions.val := by
    simpa only [functions] using ledger
  exact w.defined_float_core_functions law (final.complete w.functions.val (w.function_order law))
end Exec.Code
