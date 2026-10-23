import Exec.Interp.Simd.Common.SimdSlots
namespace Exec.Interp
open Aeneas Aeneas.Std

def simdInput (words : List U64) (position : Nat) (width : U32) : U128 :=
  if width = 2#u32 then ⟨vectorBits words position⟩
  else UScalar.cast .U128 ((words[position]?).getD 0#u64)

end Exec.Interp
