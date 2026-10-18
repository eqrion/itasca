import Exec.Code.Module.CompileSchedulerAssembly
import Exec.Code.Module.SchedulerCapacities
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Initializer lowering appends synthetic functions without changing any
source function's retained frame-capacity bound. -/
theorem CompileWitness.defined_capacities {A : Type} {allocator : runtime.platform.Alloc A}
    {bytes profile limits executable} (w : CompileWitness allocator bytes profile limits executable)
    (law : Platform.AllocCorrect allocator) {sources}
    (pending : PendingModuleCapacities profile w.env w.scheduler.functions.val sources) :
    ModuleCapacities executable sources := by
  have initialCode := pending.collected (uninitializedModule w.env w.tail profile w.functions) rfl rfl
    (w.function_order law)
  obtain ⟨source, selected, prefixCode, _⟩ := w.initializers law
  exact initialCode.extend source selected prefixCode

theorem CompileSourceCertificate.initial_capacities {A : Type} {ops : runtime.platform.Alloc A}
    {bytes profile limits executable} {w : CompileWitness ops bytes profile limits executable}
    (c : CompileSourceCertificate w) (law : Platform.AllocCorrect ops) :
    PartialModuleCapacities profile w.env (sourceFunctions c.raw) c.run.remaining.configured.functions.val := by
  have prepared := compiler_driver_configured ops law c.run
    (by simp [initialScheduler, alloc.vec.Vec.new])
    (by simp [initialScheduler, alloc.vec.Vec.new])
    (by simp [initialScheduler, alloc.vec.Vec.new])
  rw [prepared.2.2.1]
  apply PartialModuleCapacities.empty
  rw [sourceFunctions_length (by rw [c.functions, c.codeCount]), c.functions]

theorem CompileSourceCertificate.capacities_of_submission {A : Type} {ops : runtime.platform.Alloc A}
    {bytes profile limits executable} {w : CompileWitness ops bytes profile limits executable}
    (c : CompileSourceCertificate w) (law : Platform.AllocCorrect ops)
    (ledger : PartialModuleCapacities profile w.env (sourceFunctions c.raw) c.run.remaining.submitted.functions.val) :
    ModuleCapacities executable (sourceFunctions c.raw) := by
  have after := compiler_driver_after_submission ops c.run.remaining
  have functions := congrArg runtime.compiler.CompileScheduler.functions after
  have final : PartialModuleCapacities profile w.env (sourceFunctions c.raw) w.scheduler.functions.val := by
    simpa only [functions] using ledger
  exact w.defined_capacities law (final.complete w.functions.val (w.function_order law))
end Exec.Code
