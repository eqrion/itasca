import Exec.Code.Local.Relations.Common.CoreEmission
import Itasca.Spec.ScalarConst
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
theorem scalar_float_value_32 (bits : U32) :
    SpecExt.Builtins.floatOfBits 32 bits.val = ScalarConst.floatValue 23 8 bits.val := by
  have bound : bits.val < 2^32 := by scalar_tac
  have sign : (bits.val / 2^31) % 2 = 0 ↔ bits.val < 2^31 := by omega
  norm_num at sign
  simp [SpecExt.Builtins.floatOfBits, ScalarConst.floatValue, fun_M, E, signif, expon,
    SpecExt.Builtins.floatBias, sign]

theorem scalar_float_value_64 (bits : U64) :
    SpecExt.Builtins.floatOfBits 64 bits.val = ScalarConst.floatValue 52 11 bits.val := by
  have bound : bits.val < 2^64 := by scalar_tac
  have sign : (bits.val / 2^63) % 2 = 0 ↔ bits.val < 2^63 := by omega
  norm_num at sign
  simp [SpecExt.Builtins.floatOfBits, ScalarConst.floatValue, fun_M, E, signif, expon,
    SpecExt.Builtins.floatBias, sign]


end Exec.Code
