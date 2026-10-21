import Exec.Code.Module.CompileSourceCertificate
import Exec.Code.Module.CompileDriverFrame

/-! Shared scheduler configuration and code-coordinate transport for source
certificates. Function, slice and capacity proofs retain their distinct folds. -/
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Configuration facts used by each source-ordered compiler body fold. -/
theorem CompileSourceCertificate.scheduler_setup {A : Type} {ops : runtime.platform.Alloc A}
    {bytes profile limits executable} {w : CompileWitness ops bytes profile limits executable}
    (c : CompileSourceCertificate w) (law : Platform.AllocCorrect ops) :
    SignatureSequence c.run.remaining.configured.signatures.val w.env.types.val ∧
      c.run.remaining.configured.func_param_slots.val.map (fun word => word.val) =
        w.env.func_types.val.map (fun ft => signatureSlots ft.params.val) ∧
      c.run.remaining.configured.code_start.val ≤ Itasca.limits.MAX_MODULE_BYTES.val := by
  have prepared := compiler_driver_configured ops law c.run
    (by simp [initialScheduler, alloc.vec.Vec.new])
    (by simp [initialScheduler, alloc.vec.Vec.new])
    (by simp [initialScheduler, alloc.vec.Vec.new])
  refine ⟨prepared.1,prepared.2.1,?_⟩
  have bounds := code_region_spec bytes
  rw [w.region, WP.spec_ok] at bounds
  rw [prepared.2.2.2]
  change w.codeStart.val ≤ _
  exact bounds.1.trans (bounds.2.trans c.moduleBound)

/-- Transport the actual reader's code length to the coherent source slice. -/
theorem CompileSourceCertificate.code_length {A : Type} {ops : runtime.platform.Alloc A}
    {bytes profile limits executable} {w : CompileWitness ops bytes profile limits executable}
    (c : CompileSourceCertificate w) : c.run.remaining.codeLength = Slice.len c.code := by
  apply UScalar.eq_of_val_eq
  exact c.coherent.code_len_eq _ c.run.remaining.length_call
end Exec.Code
