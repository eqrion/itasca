import Itasca.Runtime.Interp.Simd.Relations.Slots

/-!
The slot-level input interpretation of SIMD operations.

Main declarations: `simdInput`. A direct consumer is `Interp.Simd.Relations.OperandsBounded`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

def simdInput (words : List U64) (position : Nat) (width : U32) : U128 :=
  if width = 2#u32 then ⟨vectorBits words position⟩
  else UScalar.cast .U128 ((words[position]?).getD 0#u64)

end Itasca.Runtime.Interp
