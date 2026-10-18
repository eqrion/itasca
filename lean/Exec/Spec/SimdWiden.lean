import Exec.Spec.SimdShiftSource
namespace Exec.Spec.Simd
open SpecExt.Builtins

def extendBits (signed : Bool) {width : Nat} (output : Nat) (bits : BitVec width) : BitVec output :=
  if signed then bits.signExtend output else bits.setWidth output

def widenBits (multiply signed : Bool) {width : Nat} (a b : BitVec width) : BitVec (width*2) :=
  if multiply then extendBits signed (width*2) a * extendBits signed (width*2) b
  else extendBits signed (width*2) a

def pairwiseBits (signed : Bool) {width : Nat} (a b : BitVec width) : BitVec (width*2) :=
  extendBits signed (width*2) a + extendBits signed (width*2) b

theorem extend_bits_source {width : Nat} (output : Nat) (signed : Bool) (bits : BitVec width)
    (le : width ≤ output) :
    uN.mk_uN (extendBits signed output bits).toNat =
      extend__ width output (if signed then .S else .U) (.mk_uN bits.toNat) := by
  cases signed
  · simp only [extendBits,Bool.false_eq_true,↓reduceIte,extend__]
    rw [BitVec.toNat_setWidth_of_le le]
  · simp only [extendBits,Bool.true_eq,↓reduceIte,extend__,proj_uN_0,Exec.Spec.signedValue_bitvec]
    rfl

inductive WidenWidth where | i8 | i16 | i32

def WidenWidth.input : WidenWidth → Jnn | .i8 => .I8 | .i16 => .I16 | .i32 => .I32

def WidenWidth.output : WidenWidth → Jnn | .i8 => .I16 | .i16 => .I32 | .i32 => .I64

def WidenWidth.width (ty : WidenWidth) : Nat := lsize (lanetype_Jnn ty.input)

def WidenWidth.count (ty : WidenWidth) : Nat := 64/ty.width

def widenHalf (high : Bool) : half := if high then .HIGH else .LOW

def widenSign (signed : Bool) : sx := if signed then .S else .U

def widenSource (ty : WidenWidth) (multiply high signed : Bool) : admininstr :=
  if multiply then
    .VEXTBINOP (.mk_ishape (shapeOf (lanetype_Jnn ty.output)))
      (.mk_ishape (shapeOf (lanetype_Jnn ty.input)))
      (.mk_vextbinop___0 ty.input (128/ty.width) ty.output ty.count (.EXTMUL (widenHalf high) (widenSign signed)))
  else
    .VCVTOP (shapeOf (lanetype_Jnn ty.output)) (shapeOf (lanetype_Jnn ty.input))
      (.mk_vcvtop___0 ty.input (128/ty.width) ty.output ty.count (.EXTEND (widenHalf high) (widenSign signed)))

inductive PairwiseWidth where | i8 | i16

def PairwiseWidth.widen : PairwiseWidth → WidenWidth | .i8 => .i8 | .i16 => .i16

def pairwiseSource (ty : PairwiseWidth) (signed : Bool) : admininstr :=
  .VEXTUNOP (.mk_ishape (shapeOf (lanetype_Jnn ty.widen.output)))
    (.mk_ishape (shapeOf (lanetype_Jnn ty.widen.input)))
    (.mk_vextunop___0 ty.widen.input (128/ty.widen.width) ty.widen.output ty.widen.count (.EXTADD_PAIRWISE (widenSign signed)))
end Exec.Spec.Simd
