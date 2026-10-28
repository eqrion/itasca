import Itasca.Runtime.Representation.Encoding
import Itasca.Runtime.Abs.Float.Descriptor
namespace Itasca.Runtime.Code
open SpecExt.Builtins SpecExt.Builtins.Float

theorem encode_float_number (ty : numtype) (bits : Nat) (bound : bits < 2^sizenn ty) :
    encodeValue (.CONST ty (Abs.Float.numberOfBits ty bits)) = [bits] := by
  cases ty
  · rfl
  · rfl
  · change [floatBits 32 (floatOfBits 32 bits)] = [bits]
    rw [float_bits_roundtrip_32 bits bound]
  · change [floatBits 64 (floatOfBits 64 bits)] = [bits]
    rw [float_bits_roundtrip_64 bits bound]

theorem encode_float_operands (op : Abs.Float.Instruction) (a b : Nat)
    (first : a < 2^sizenn op.input) (second : b < 2^sizenn op.input) :
    encodeValues (op.operands a b) = if op.arity = 1 then [a] else [a,b] := by
  unfold Abs.Float.Instruction.operands
  split
  all_goals simp only [encodeValues, List.flatMap_cons, List.flatMap_nil,
    encode_float_number _ _ first, encode_float_number _ _ second, List.append_nil, List.singleton_append]
end Itasca.Runtime.Code
