import Itasca.Runtime.Code.Module.CompileEntry
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- The driver's issued byte cap and the scanned code origin bound all
absolute positions in an actually dispatched compiler batch. -/
theorem CompileEntryWitness.coordinate_bound {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.CodeBatch}
    (w : CompileEntryWitness ops before after batch finalBatch)
    {issued : StreamBatch.Issued} (reachable : StreamBatch.Reachable issued batch)
    (bounded : issued.Bounded) (origin : before.code_start.val ≤ limits.MAX_MODULE_BYTES.val) :
    w.batchStart.val + w.dispatched.code.length ≤ Usize.max := by
  have identity := (StreamBatch.Reachable.dispatch reachable w.dispatch).validation.1
  obtain ⟨_, _, _, code, offset, _, _, _⟩ := identity
  have arithmetic := UScalar.add_equiv before.code_start w.dispatched.code_offset
  rw [w.coordinates] at arithmetic
  have position := arithmetic.2.1
  have cap : limits.MAX_MODULE_BYTES.val + limits.MAX_MODULE_BYTES.val ≤ Usize.max := by
    simp only [limits.MAX_MODULE_BYTES]
    scalar_tac
  have size := bounded.2.2
  rw [code, offset] at *
  omega

/-- The successful entry's exact body span discharges the function-start
absolute-end premise; it need not be assumed independently by compilation. -/
theorem CompileEntryWitness.end_fits {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.CodeBatch}
    (w : CompileEntryWitness ops before after batch finalBatch)
    {issued : StreamBatch.Issued} (reachable : StreamBatch.Reachable issued batch)
    (bounded : issued.Bounded) (origin : before.code_start.val ≤ limits.MAX_MODULE_BYTES.val)
    {finish : Usize}
    (entry : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      w.dispatched.code w.dispatched.env w.entry.index w.dispatched.validated_end finish
      w.initial w.final w.dispatched.profile) :
    w.batchStart.val + finish.val ≤ Usize.max := by
  have bound := w.coordinate_bound reachable bounded origin
  have span := entry.body_bytes.bound
  omega
end Itasca.Runtime.Code
