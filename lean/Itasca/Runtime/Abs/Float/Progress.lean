import Itasca.Runtime.Abs.Float.Results
import Itasca.Runtime.Spec.FloatReinterpret
namespace Itasca.Runtime.Abs.Float
open SpecExt SpecExt.Builtins SpecExt.Builtins.Float

theorem integer_number_bound (target : Inn) (bits : Nat)
    (valid : wf_num_ (numtype_Inn target) (.mk_num__0 target (.mk_uN bits))) :
    bits < 2^sizenn (numtype_Inn target) := by
  cases valid with
  | num__case_0 _ _ sizePresent bounded same =>
    cases bounded with
    | uN_case_0 _ limit =>
      cases target <;> norm_num [sizenn, numtype_Inn, valtype_numtype, valtype_Inn, size] at limit ⊢ <;> omega

end Itasca.Runtime.Abs.Float
