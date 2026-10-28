import Exec.Interp.Numeric.Float.FloatPromote
import Exec.Spec.FloatPromote

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt SpecExt.Builtins SpecExt.Builtins.Float

theorem scalar_f64_promote_f32_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 187#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .CVTOP .F64 .F32 (.mk_cvtop___3 .F32 .F64 .PROMOTE)]
        [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_promote_f32 ops a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.numeric_conversion_pure _ _ _ _ _ _ (Spec.float_promote_relation _)
  · exact List.mem_map.mpr ⟨_, chosen, rfl⟩
  · exact Spec.float_num_wf .F32 _ (floatOfBits_wf 32 (by omega) _)
  · exact Spec.float_num_wf .F64 _ (floatOfBits_wf 64 (by omega) _)
  · exact .cvtop___case_3 _ _ _ _ _ (.cvtop__Fnn_1_Fnn_2_case_0 _ _ (by decide)) rfl rfl
  · decide

end Itasca.Runtime.Interp
