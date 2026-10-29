import Itasca.Runtime.Interp.Simd.Integer.UnaryAll
import Itasca.Runtime.Spec.Simd.AllTrue

/-!
Lane and dispatch correspondence for all-true reduction.

Main declarations: `all_true_lanes_sound` and `all_true_dispatch_eq`. A direct consumer is `Interp.Simd.Execution.PureUnary`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd SpecExt.Builtins
@[step] theorem all_true_lanes_sound (ty : Jnn) (x : U128) :
    runtime.interp.simd.integer_unary_lanes (unaryOpcode ty .allTrue) x
      ⦃ result => Step_pure [.VCONST .V128 (.mk_uN x.val),allTrueSource ty]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN result.val))] ⦄ := by
  apply WP.spec_mono (integer_unary_lanes ty .allTrue x)
  intro result outcome
  have truth := unary_all_iff (lsize (lanetype_Jnn ty)) x.bv
    (128/lsize (lanetype_Jnn ty)) (by cases ty <;> decide)
  have source := all_true_step ty x.bv
    (unaryAll (lsize (lanetype_Jnn ty)) x.bv (128/lsize (lanetype_Jnn ty))) truth
  change result = UScalar.cast .U128 (UScalar.cast_fromBool .U32 _) at outcome
  subst result
  cases h : unaryAll (lsize (lanetype_Jnn ty)) x.bv (128/lsize (lanetype_Jnn ty)) <;>
    simp only [h,Bool.false_eq_true,ite_false,ite_true] at source ⊢ <;>
    with_unfolding_all exact source

theorem all_true_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Jnn) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (unaryOpcode ty .allTrue) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.integer_unary_lanes (unaryOpcode ty .allTrue) x)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  cases ty <;> unfold runtime.interp.simd.simd unaryOpcode <;> with_unfolding_all rfl
end Itasca.Runtime.Interp.Simd
