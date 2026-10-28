import Itasca.Runtime.Interp.Simd.Common.SimdShiftBits
import Itasca.Runtime.Interp.Numeric.Integer.IntCounts
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

def unaryWord (action : U32) (value : U64) (signedValue : I64) : U64 :=
  match action with
  | 0#uscalar => if signedValue < 0#i64
      then core.num.U64.wrapping_sub 0#u64 (IScalar.hcast .U64 signedValue)
      else IScalar.hcast .U64 signedValue
  | 1#uscalar => core.num.U64.wrapping_sub 0#u64 value
  | 2#uscalar => UScalar.cast .U64 (⟨BitVec.ofNat 32 (Primitive.countBits 64 value.val)⟩ : U32)
  | _ => value

theorem unary_word (action : U32) (value : U64) (signedValue : I64) :
    (match action with
      | 0#uscalar => if signedValue < 0#i64
          then Aeneas.Std.bind (Aeneas.Std.lift (IScalar.hcast .U64 signedValue))
            (fun cast => Result.ok (core.num.U64.wrapping_sub 0#u64 cast))
          else Result.ok (IScalar.hcast .U64 signedValue)
      | 1#uscalar => Result.ok (core.num.U64.wrapping_sub 0#u64 value)
      | 2#uscalar => Aeneas.Std.bind (core.num.U64.count_ones value)
          (fun count => Result.ok (UScalar.cast .U64 count))
      | _ => Result.ok value) = .ok (unaryWord action value signedValue) := by
  unfold unaryWord
  split
  · split <;> simp only [Aeneas.Std.lift,Aeneas.Std.bind_ok]
  · rfl
  · simp only [core.num.U64.count_ones,bind_ok]
  · rfl

@[step] theorem unary_word_effect (action : U32) (value : U64) (signedValue : I64) :
    (match action with
      | 0#uscalar => if signedValue < 0#i64 then
          Aeneas.Std.bind (Aeneas.Std.lift (IScalar.hcast .U64 signedValue))
            (fun cast => Result.ok (core.num.U64.wrapping_sub 0#u64 cast))
        else Result.ok (IScalar.hcast .U64 signedValue)
      | 1#uscalar => Result.ok (core.num.U64.wrapping_sub 0#u64 value)
      | 2#uscalar => Aeneas.Std.bind (core.num.U64.count_ones value)
          (fun count => Result.ok (UScalar.cast .U64 count))
      | _ => Result.ok value) ⦃ out => out = unaryWord action value signedValue ⦄ := by
  rw [unary_word]
  exact WP.spec.ret rfl

def unaryLane (action : U32) (width : Nat) (bits : BitVec width) : BitVec width :=
  (unaryWord action ⟨bits.setWidth 64⟩ ⟨bits.signExtend 64⟩).bv.setWidth width

def unaryAll (width : Nat) (x : BitVec 128) : Nat → Bool
  | 0 => true
  | n+1 => unaryAll width x n && ((⟨(laneBits width n x).setWidth 64⟩ : U64) != 0#u64)

def unarySigns (width : Nat) (x : BitVec 128) : Nat → BitVec 32
  | 0 => 0
  | n+1 => unarySigns width x n |||
      ((((laneBits width n x).setWidth 64 >>> (width-1)).setWidth 32) <<< n)
end Itasca.Runtime.Interp.Simd
