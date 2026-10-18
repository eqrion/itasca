import SpecExt.Builtins.Float.Repr

/-! Round-to-nearest, ties-to-even on exact rational magnitudes. Positive finite
IEEE encodings are ordered by their numeric value. Binary search selects the
adjacent encodings; their midpoint selects the result. The successor of the
largest finite value is the exact power of two at the overflow boundary, whose
encoding rounds to infinity. Square-root rounding compares exact squares of
these midpoints, avoiding a native floating-point or real-number oracle. -/

namespace SpecExt.Builtins.Float

def infinityBits (width : Nat) : Nat := (2 ^ E width - 1) * 2 ^ fun_M width

/-- Finite value at a positive encoding; the infinity encoding is interpreted
as the next exact power of two solely for rounding and overflow decisions. -/
def roundingValue (width bits : Nat) : Rat :=
  if bits = infinityBits width then powTwo ((floatBias width : Int) + 1)
  else magnitudeValue width (magnitude (floatOfBits width bits))

/-- Upper-bound binary search on an inclusive interval. `width` iterations
suffice for a valid IEEE width because the interval has fewer than 2^width entries. -/
def floorEncoding (width : Nat) (square : Bool) (q : Rat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
      let mid := (lo + hi + 1) / 2
      let value := roundingValue width mid
      let key := if square then value * value else value
      if key ≤ q then floorEncoding width square q fuel mid hi
      else floorEncoding width square q fuel lo (mid - 1)

def roundMagnitude (width : Nat) (square : Bool) (q : Rat) : fNmag :=
  let lo := floorEncoding width square q width 0 (infinityBits width - 1)
  let midpoint := (roundingValue width lo + roundingValue width (lo + 1)) / 2
  let key := if square then midpoint * midpoint else midpoint
  let bits := if q < key then lo else if key < q then lo + 1
    else if lo % 2 = 0 then lo else lo + 1
  magnitude (floatOfBits width bits)

/-- The separate zero sign is used only for an exact zero. Nonzero values that
underflow retain their mathematical sign. -/
def round (width : Nat) (q : Rat) (negativeZero : Bool := false) : fN :=
  if q = 0 then withSign negativeZero (.SUBNORM 0)
  else if q < 0 then .NEG (roundMagnitude width false (-q))
  else .POS (roundMagnitude width false q)

def roundSqrt (width : Nat) (q : Rat) : fN :=
  .POS (roundMagnitude width true q)

end SpecExt.Builtins.Float
