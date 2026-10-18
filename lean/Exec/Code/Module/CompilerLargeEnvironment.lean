import Exec.Code.Module.Stream
import Itasca.Stream.DriverTotal
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- An oversized scanned environment is rejected before any compiler callback.
This covers custom compile limits larger than the validator's module cap. -/
theorem compiler_stream_large_environment {V : Type} (visitor : stream.StreamingVisitor V)
    (profile : ValidationProfile) (source : runtime.compiler.CompileSource)
    (bounds : SourceBounds source) (large : limits.MAX_MODULE_BYTES.val < source.code_start.val)
    (state : V) (storage : module.Env) :
    stream.validate_streaming runtime.compiler.CompileSource.Insts.ItascaStreamSource visitor
      0#u64 profile source state storage = .ok (.Err .ModuleTooLarge,state,storage) := by
  obtain ⟨_,environment,bytes,rfl,decoded⟩ := WP.spec_imp_exists (source_environment_spec source bounds)
  have length : bytes.length = source.code_start.val := by
    simp only [Slice.length,decoded,sourceEnvironment,List.length_take]
    have bound := bounds.1.trans bounds.2
    change source.code_start.val ≤ source.bytes.val.length at bound
    omega
  obtain ⟨result,checked,post⟩ := WP.spec_imp_exists (limits.add_offset.spec 0#usize (Slice.len bytes))
  have rejected : result = .Err .ModuleTooLarge := by
    cases result with
    | Err error => exact congrArg core.result.Result.Err post.1
    | Ok total =>
      have bound := post.2
      have count := post.1
      simp only [show (0#usize).val = 0 from rfl,Slice.len_val] at count
      omega
  simp only [Exec.stream.validate_streaming, Itasca.stream.validate_streaming]
  simp only [environment]
  simp only [bind_ok,core.result.Result.Insts.CoreOpsTry.branch]
  rw [checked,rejected]
  simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
end Exec.Code
