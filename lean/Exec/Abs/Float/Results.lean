import Exec.Abs.Float.Instruction
import Exec.Spec.FloatSigns
import Exec.Spec.FloatMinMax
import Exec.Spec.FloatPromote
import Exec.Spec.FloatComparison
import SpecExt.Builtins.Float.Canonical

namespace Itasca.Runtime.Abs.Float
open SpecExt SpecExt.Builtins SpecExt.Builtins.Float

theorem numberOfBits_float (ty : Fnn) (bits : Nat) :
    numberOfBits (numtype_Fnn ty) bits = .mk_num__1 ty (floatOfBits (sizenn (numtype_Fnn ty)) bits) := by
  cases ty <;> rfl

theorem numberOfBits_integer (ty : Inn) (bits : Nat) :
    numberOfBits (numtype_Inn ty) bits = .mk_num__0 ty (.mk_uN bits) := by
  cases ty <;> rfl

theorem float_encoding (ty : Fnn) (value : fN) (valid : wf_fN (sizenn (numtype_Fnn ty)) value) :
    ∃ bits, bits < 2^sizenn (numtype_Fnn ty) ∧ floatOfBits (sizenn (numtype_Fnn ty)) bits = value := by
  cases ty
  · exact ⟨floatBits 32 value, floatBits_lt_32 value valid, float_roundtrip_32 value valid⟩
  · exact ⟨floatBits 64 value, floatBits_lt_64 value valid, float_roundtrip_64 value valid⟩

end Itasca.Runtime.Abs.Float
