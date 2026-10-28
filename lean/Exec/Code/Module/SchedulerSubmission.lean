import Exec.Code.Module.CompileSubmit
import Exec.Code.Module.CollectFunctions
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Metadata captured before any function compilation is fixed across all
actual entry calls in a submitted batch. -/
def schedulerStatic {A : Type} (scheduler : runtime.compiler.CompileScheduler A) :=
  (scheduler.signatures, scheduler.func_param_slots, scheduler.code_start)

theorem CompileEntryWitness.static {A : Type} {allocator : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.CodeBatch}
    (w : CompileEntryWitness allocator before after batch finalBatch) :
    schedulerStatic after = schedulerStatic before := by rw [w.published]; rfl

theorem CompileEntries.static {A : Type} {allocator : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.CodeBatch}
    (run : CompileEntries allocator before batch after finalBatch) :
    schedulerStatic after = schedulerStatic before := by
  induction run with
  | nil => rfl
  | next entry rest ih =>
    obtain ⟨w⟩ := compile_entry_accepted _ _ _ _ _ entry
    exact ih.trans w.static

end Itasca.Runtime.Code
