import SpecExt.Builtins.Bits

/-!
Integer builtin definitions transcribed from the pinned numerical prose:
`vendor/spectec/document/core/exec/numerics.rst`, integer and conversion sections.
Widths and input ranges are the generated `wf_*` premises, not dependent types.
Definitions are total outside those premises, without a Wasm correctness claim
there. In particular, average exists only unsigned and Q15 multiply only signed
at width 16; unsupported cases return zero.

Signed narrowing interprets the *source* as signed even for an unsigned target.
Arithmetic right shift uses floor division, whereas rational truncation uses
truncation toward zero. These operations differ on negative inputs.
-/

namespace SpecExt.Builtins

/-- Two's-complement signed interpretation of a valid width-bit input. -/
def signedValue (width value : Nat) : Int :=
  if value < 2 ^ (width - 1) then value else (value : Int) - (2 : Int) ^ width

/-- Width-bit encoding, also total on integers outside the representable range. -/
def encodeSigned (width : Nat) (value : Int) : iN :=
  .mk_uN (value % (2 : Int) ^ width).toNat

/-- Saturation to the target signed or unsigned range, followed by encoding. -/
def saturate (width : Nat) (sign : sx) (value : Int) : iN :=
  match sign with
  | .U => .mk_uN (max 0 (min value ((2 : Int) ^ width - 1))).toNat
  | .S => encodeSigned width
      (max (-((2 : Int) ^ (width - 1))) (min value ((2 : Int) ^ (width - 1) - 1)))

def leadingZeros : List bit → Nat
  | .mk_bit 0 :: rest => 1 + leadingZeros rest
  | _ => 0

def population : List bit → Nat
  | [] => 0
  | .mk_bit value :: rest => value + population rest

end SpecExt.Builtins

/-- A nonnegative s33 type index is the same u32 index; negative s33 values
encode value types instead and are outside this conversion's intended domain. -/
def s33_to_u32 (v_s33 : s33) : u32 := .mk_uN (proj_sN_0 v_s33).toNat

/-- Rational truncation toward zero, including negative nonintegral inputs. -/
def truncz (rat : Rat) : Int := rat.num.tdiv (Int.ofNat rat.den)

def extend__ (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN) : iN :=
  match v_sx with
  | .U => v_iN
  | .S => SpecExt.Builtins.encodeSigned v_N
      (SpecExt.Builtins.signedValue v_M (proj_uN_0 v_iN))

def wrap__ (_v_M : M) (v_N : N) (v_iN : iN) : iN :=
  .mk_uN (proj_uN_0 v_iN % 2 ^ v_N)

def narrow__ (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN) : iN :=
  SpecExt.Builtins.saturate v_N v_sx
    (SpecExt.Builtins.signedValue v_M (proj_uN_0 v_iN))

def iclz_ (v_N : N) (v_iN : iN) : iN :=
  .mk_uN (SpecExt.Builtins.leadingZeros (ibits_ v_N v_iN))

def ictz_ (v_N : N) (v_iN : iN) : iN :=
  .mk_uN (SpecExt.Builtins.leadingZeros (ibits_ v_N v_iN).reverse)

def ipopcnt_ (v_N : N) (v_iN : iN) : iN :=
  .mk_uN (SpecExt.Builtins.population (ibits_ v_N v_iN))

def iand_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN :=
  inv_ibits_ v_N (List.zipWith (fun (.mk_bit a) (.mk_bit b) => .mk_bit (a * b))
    (ibits_ v_N v_iN) (ibits_ v_N iN_0))

def ior_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN :=
  inv_ibits_ v_N (List.zipWith (fun (.mk_bit a) (.mk_bit b) => .mk_bit (max a b))
    (ibits_ v_N v_iN) (ibits_ v_N iN_0))

def ixor_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN :=
  inv_ibits_ v_N (List.zipWith (fun (.mk_bit a) (.mk_bit b) => .mk_bit ((a + b) % 2))
    (ibits_ v_N v_iN) (ibits_ v_N iN_0))

def inot_ (v_N : N) (v_iN : iN) : iN :=
  inv_ibits_ v_N ((ibits_ v_N v_iN).map (fun (.mk_bit a) => .mk_bit (1 - a)))

def irev_ (v_N : N) (v_iN : iN) : iN :=
  inv_ibits_ v_N (ibits_ v_N v_iN).reverse

def iandnot_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN :=
  iand_ v_N v_iN (inot_ v_N iN_0)

def ibitselect_ (v_N : N) (v_iN : iN) (iN_0 : iN) (iN_1 : iN) : iN :=
  ior_ v_N (iand_ v_N v_iN iN_1) (iandnot_ v_N iN_0 iN_1)

def ishl_ (v_N : N) (v_iN : iN) (v_u32 : u32) : iN :=
  .mk_uN ((proj_uN_0 v_iN * 2 ^ (proj_uN_0 v_u32 % v_N)) % 2 ^ v_N)

def ishr_ (v_N : N) (v_sx : sx) (v_iN : iN) (v_u32 : u32) : iN :=
  let shift := proj_uN_0 v_u32 % v_N
  match v_sx with
  | .U => .mk_uN (proj_uN_0 v_iN / 2 ^ shift)
  | .S => SpecExt.Builtins.encodeSigned v_N
      (SpecExt.Builtins.signedValue v_N (proj_uN_0 v_iN) / (2 : Int) ^ shift)

def irotl_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN :=
  let bits := ibits_ v_N v_iN
  let shift := proj_uN_0 iN_0 % v_N
  inv_ibits_ v_N (bits.drop shift ++ bits.take shift)

def irotr_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN :=
  let bits := ibits_ v_N v_iN
  let split := v_N - proj_uN_0 iN_0 % v_N
  inv_ibits_ v_N (bits.drop split ++ bits.take split)

def iavgr_ (_v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) : iN :=
  match v_sx with
  | .U => .mk_uN ((proj_uN_0 v_iN + proj_uN_0 iN_0 + 1) / 2)
  | .S => .mk_uN 0

def iq15mulr_sat_ (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) : iN :=
  match v_N, v_sx with
  | 16, .S =>
      let a := SpecExt.Builtins.signedValue 16 (proj_uN_0 v_iN)
      let b := SpecExt.Builtins.signedValue 16 (proj_uN_0 iN_0)
      SpecExt.Builtins.saturate 16 .S ((a * b + 2 ^ 14) / 2 ^ 15)
  | _, _ => .mk_uN 0
