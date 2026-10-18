import Wasm2Prefix

/-! Integer bit lists follow the pinned numerics prose: most significant bit first.
Byte sequences, separately, are little-endian. Floating-point packing follows the IEEE sign/exponent/fraction formulas in
the pinned Wasm 1.0/2.0 numerical prose, including signed zero and NaN payloads. -/

namespace SpecExt.Builtins

/-- The low `width` bits, in the prose's most-significant-first order. -/
def integerBits : Nat → Nat → List bit
  | 0, _ => []
  | width + 1, value => .mk_bit ((value / 2 ^ width) % 2) :: integerBits width value

/-- Interpret a most-significant-first list; callers provide exactly N valid bits. -/
def integerOfBits : List bit → Nat
  | [] => 0
  | .mk_bit value :: rest => value * 2 ^ rest.length + integerOfBits rest

end SpecExt.Builtins

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:76.1-76.102 -/
def ibits_ (v_N : N) (v_iN : iN) : List bit :=
  SpecExt.Builtins.integerBits v_N (proj_uN_0 v_iN)


namespace SpecExt.Builtins

/-- IEEE exponent bias for the generated binary format parameters. -/
def floatBias (width : Nat) : Nat := 2 ^ (E width - 1) - 1

/-- Pack a magnitude into its exponent and fraction fields. -/
def magnitudeBits (width : Nat) : fNmag → Nat
  | .NORM fraction exponent =>
      (exponent + (floatBias width : Int)).toNat * 2 ^ fun_M width + fraction
  | .SUBNORM fraction => fraction
  | .INF => (2 ^ E width - 1) * 2 ^ fun_M width
  | .NAN payload => (2 ^ E width - 1) * 2 ^ fun_M width + payload

def floatBits (width : Nat) : fN → Nat
  | .POS mag => magnitudeBits width mag
  | .NEG mag => 2 ^ (width - 1) + magnitudeBits width mag

/-- Decode every bit pattern of the selected IEEE binary format. -/
def floatOfBits (width value : Nat) : fN :=
  let fraction := value % 2 ^ fun_M width
  let exponent := (value / 2 ^ fun_M width) % 2 ^ E width
  let mag := if exponent = 0 then fNmag.SUBNORM fraction
    else if exponent = 2 ^ E width - 1 then
      if fraction = 0 then fNmag.INF else fNmag.NAN fraction
    else fNmag.NORM fraction ((exponent : Int) - floatBias width)
  if (value / 2 ^ (width - 1)) % 2 = 0 then .POS mag else .NEG mag

end SpecExt.Builtins

def fbits_ (v_N : N) (v_fN : fN) : List bit :=
  SpecExt.Builtins.integerBits v_N (SpecExt.Builtins.floatBits v_N v_fN)


/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:83.1-83.85 -/
def inv_ibits_ (_v_N : N) (var_0_lst : List bit) : iN :=
  .mk_uN (SpecExt.Builtins.integerOfBits var_0_lst)


/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:84.1-84.85 -/
def inv_fbits_ (v_N : N) (var_0_lst : List bit) : fN :=
  SpecExt.Builtins.floatOfBits v_N (SpecExt.Builtins.integerOfBits var_0_lst)
