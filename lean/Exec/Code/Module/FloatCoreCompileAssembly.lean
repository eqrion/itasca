import Exec.Code.Module.CompileEntry
import Exec.Code.Local.Initializer.InitializerComplete
import Exec.Code.Module.FloatCoreCollectedFunctions
import Exec.Code.Module.CompileAssembly
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
theorem CompileWitness.defined_float_core_functions {A : Type} {allocator : runtime.platform.Alloc A}
    {bytes profile limits executable} (w : CompileWitness allocator bytes profile limits executable)
    (law : Platform.AllocCorrect allocator) {sources}
    (pending : PendingFloatCoreModuleFunctions w.env w.scheduler.functions.val sources) :
    FloatCoreModuleFunctions executable sources ∧ InitializerMappings executable := by
  have initialCode := pending.collected (uninitializedModule w.env w.tail profile w.functions) rfl
    (w.function_order law)
  obtain ⟨source, _, prefixCode, initializers⟩ := w.initializers law
  exact ⟨initialCode.extend source prefixCode, initializers⟩
end Exec.Code
