import Itasca.Runtime.Code.Module.CompileEntry
import Itasca.Runtime.Code.Local.Initializer.InitializerComplete
import Itasca.Runtime.Code.Module.ExecutableCollectedFunctions
import Itasca.Runtime.Code.Module.CompileAssembly
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca
theorem CompileWitness.defined_executable_functions {A : Type} {allocator : runtime.platform.Alloc A}
    {bytes profile limits executable} (w : CompileWitness allocator bytes profile limits executable)
    (law : Platform.AllocCorrect allocator) {sources}
    (pending : PendingExecutableModuleFunctions w.env w.scheduler.functions.val sources) :
    ExecutableModuleFunctions executable sources ∧ InitializerMappings executable := by
  have initialCode := pending.collected (uninitializedModule w.env w.tail profile w.functions) rfl
    (w.function_order law)
  obtain ⟨source, _, prefixCode, initializers⟩ := w.initializers law
  exact ⟨initialCode.extend source prefixCode, initializers⟩
end Itasca.Runtime.Code
