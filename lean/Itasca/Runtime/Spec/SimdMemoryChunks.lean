import Itasca.Runtime.Spec.MemoryStore
import Itasca.Runtime.Spec.SimdWiden
namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem integerBytes_take (count total value : Nat) (le : count ≤ total) :
    (integerBytes total value).take count = integerBytes count value := by
  induction count generalizing total value with
  | zero => simp [integerBytes]
  | succ count ih =>
    cases total with
    | zero => omega
    | succ total =>
      simpa only [integerBytes,List.take_succ_cons] using
        congrArg (List.cons (.mk_byte (value%256))) (ih total (value/256) (by omega))

theorem integerBytes_drop (start total value : Nat) (le : start ≤ total) :
    (integerBytes total value).drop start = integerBytes (total-start) (value/256^start) := by
  induction start generalizing total value with
  | zero => simp
  | succ start ih =>
    cases total with
    | zero => omega
    | succ total =>
      simp only [integerBytes,List.drop_succ_cons]
      rw [ih total (value/256) (by omega)]
      simp only [Nat.div_div_eq_div_mul,Nat.pow_succ,Nat.mul_comm 256,Nat.add_sub_add_right]

theorem integerBytes_chunk (width index value : Nat) (fit : index*width+width ≤ 8) :
    (integerBytes 8 value |>.drop (index*width) |>.take width) =
      integerBytes width ((value/256^(index*width))%256^width) := by
  rw [integerBytes_drop _ _ _ (by omega),integerBytes_take _ _ _ (by omega),integerBytes_mod]
end Itasca.Runtime.Spec.Simd
