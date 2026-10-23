import Exec.Interp.Simd.Common.SimdExtractRuntime
import Exec.Spec.SimdExtract
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

theorem extract_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : lanetype) (offset laneIndex : U32) (bits a b c : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (extractOpcode ty) offset laneIndex bits a b c memory =
      Aeneas.Std.bind (runtime.interp.simd.access_lane (extractOpcode ty) laneIndex a b)
        (fun result => Result.ok (result, memory)) := by
  cases ty <;> unfold runtime.interp.simd.simd extractOpcode <;> with_unfolding_all rfl

end Exec.Interp.Simd
