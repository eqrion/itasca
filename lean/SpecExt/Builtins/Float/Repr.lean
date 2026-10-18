import SpecExt.Builtins.Bits

/-! Exact rational interpretation of finite IEEE values and the permitted NaN
sets. The definitions follow the pinned numerical prose. Sign is kept separately
so zero, infinity, and NaN payloads do not lose their representation. -/

namespace SpecExt.Builtins.Float

def negative : fN → Bool
  | .POS _ => false
  | .NEG _ => true

def magnitude : fN → fNmag
  | .POS value | .NEG value => value

def withSign (neg : Bool) (value : fNmag) : fN :=
  if neg then .NEG value else .POS value

def isNaN (value : fN) : Bool :=
  match magnitude value with
  | .NAN _ => true
  | _ => false

def isInf (value : fN) : Bool := magnitude value == .INF

def isZero (value : fN) : Bool := magnitude value == .SUBNORM 0

def powTwo (exponent : Int) : Rat :=
  if exponent < 0 then 1 / ((2 : Rat) ^ exponent.natAbs)
  else (2 : Rat) ^ exponent.toNat

/-- Numeric value of finite magnitudes. Infinity/NaN use zero only as a total
extension; every arithmetic caller handles those constructors first. -/
def magnitudeValue (width : Nat) : fNmag → Rat
  | .NORM fraction exponent =>
      ((2 ^ fun_M width + fraction : Nat) : Rat) * powTwo (exponent - fun_M width)
  | .SUBNORM fraction =>
      (fraction : Rat) * powTwo (1 - (floatBias width : Int) - fun_M width)
  | .INF | .NAN _ => 0

def finiteValue (width : Nat) (value : fN) : Rat :=
  let q := magnitudeValue width (magnitude value)
  if negative value then -q else q

def canonicalInput (width : Nat) (value : fN) : Bool :=
  match magnitude value with
  | .NAN payload => payload == canon_ width
  | _ => true

/-- Both signs of each arithmetic payload, as permitted by the Wasm prose.
This finite list is a specification, not a runtime enumeration. -/
def arithmeticNaNs (width : Nat) : List fN :=
  (List.range (canon_ width)).flatMap fun offset =>
    [.POS (.NAN (canon_ width + offset)), .NEG (.NAN (canon_ width + offset))]

def canonicalNaNs (width : Nat) : List fN :=
  [.POS (.NAN (canon_ width)), .NEG (.NAN (canon_ width))]

def nans (width : Nat) (inputs : List fN) : List fN :=
  if inputs.all (canonicalInput width) then canonicalNaNs width else arithmeticNaNs width

/-- Equality is false for every NaN, and identifies the two zeros. -/
def equal (width : Nat) (a b : fN) : Bool :=
  if isNaN a || isNaN b then false
  else if isInf a || isInf b then a == b
  else finiteValue width a == finiteValue width b

/-- Strict IEEE comparison, including infinities and signed zeros. -/
def less (width : Nat) (a b : fN) : Bool :=
  if isNaN a || isNaN b then false
  else if isInf a then
    if negative a then !(isInf b && negative b) else false
  else if isInf b then !negative b
  else decide (finiteValue width a < finiteValue width b)

end SpecExt.Builtins.Float
