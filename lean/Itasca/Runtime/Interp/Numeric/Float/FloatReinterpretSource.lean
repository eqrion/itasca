import Itasca.Runtime.Interp.Numeric.Float.Float
import Itasca.Runtime.Spec.FloatReinterpret

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt SpecExt.Builtins SpecExt.Builtins.Float

theorem scalar_f64_reinterpret_i64_source {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 191#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .I64 (.mk_num__0 .I64 (.mk_uN a.val)), .CVTOP .F64 .I64 (.mk_cvtop___1 .I64 .F64 .REINTERPRET)]
        [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 value.val))] ⦄ := by
  have run : runtime.interp.float.scalar ops 191#u16 a b = .ok (.Ok (a)) := by
    unfold runtime.interp.float.scalar
    with_unfolding_all rfl
  rw [run]
  simp only [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  exact Spec.f64_reinterpret_i64_pure _ (by scalar_tac)

theorem scalar_i64_reinterpret_f64_source {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 189#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)), .CVTOP .I64 .F64 (.mk_cvtop___2 .F64 .I64 .REINTERPRET)]
        [.CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val))] ⦄ := by
  have run : runtime.interp.float.scalar ops 189#u16 a b = .ok (.Ok (a)) := by
    unfold runtime.interp.float.scalar
    with_unfolding_all rfl
  rw [run]
  simp only [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  exact Spec.i64_reinterpret_f64_pure _ (by scalar_tac)

end Itasca.Runtime.Interp
