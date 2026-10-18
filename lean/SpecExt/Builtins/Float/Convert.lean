import SpecExt.Builtins.Float.Arith

/-! Floating conversions: exact integer truncation and saturation; rational
rounding for integer conversion and format conversion; representation-preserving
reinterpretation. Canonical NaN classification uses the source format. -/

open SpecExt.Builtins SpecExt.Builtins.Float

def convert__ (source target : Nat) (sign : sx) (value : iN) : fN :=
  let integer : Int := match sign with
    | .S => signedValue source (proj_uN_0 value)
    | .U => proj_uN_0 value
  round target (integer : Rat)

def demote__ (source target : Nat) (value : fN) : List fN :=
  if isNaN value then
    if canonicalInput source value then canonicalNaNs target else arithmeticNaNs target
  else if isInf value || isZero value then [value]
  else [round target (finiteValue source value)]

/-- For the valid widening pair, rounding is exact. The same total format
conversion also defines behavior on other width pairs, outside this builtin's domain. -/
def promote__ (source target : Nat) (value : fN) : List fN := demote__ source target value

def trunc__ (source target : Nat) (sign : sx) (value : fN) : Option iN :=
  if isNaN value || isInf value then none
  else
    let integer := truncz (finiteValue source value)
    let lower : Int := match sign with | .S => -(2 : Int) ^ (target - 1) | .U => 0
    let upper : Int := match sign with | .S => (2 : Int) ^ (target - 1) | .U => 2 ^ target
    if lower ≤ integer ∧ integer < upper then some (encodeSigned target integer) else none

def trunc_sat__ (source target : Nat) (sign : sx) (value : fN) : Option iN :=
  if isNaN value then some (.mk_uN 0)
  else if isInf value then
    some (saturate target sign (if negative value then -(2 : Int) ^ target else 2 ^ target))
  else some (saturate target sign (truncz (finiteValue source value)))

def reinterpret__ (source target : numtype) (value : num_) : num_ :=
  match source, target, value with
  | .I32, .F32, .mk_num__0 _ bits => .mk_num__1 .F32 (floatOfBits 32 (proj_uN_0 bits))
  | .I64, .F64, .mk_num__0 _ bits => .mk_num__1 .F64 (floatOfBits 64 (proj_uN_0 bits))
  | .F32, .I32, .mk_num__1 _ f => .mk_num__0 .I32 (.mk_uN (floatBits 32 f))
  | .F64, .I64, .mk_num__1 _ f => .mk_num__0 .I64 (.mk_uN (floatBits 64 f))
  | _, _, _ => value
