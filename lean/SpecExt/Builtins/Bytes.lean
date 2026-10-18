import SpecExt.Builtins.Bits

/-! Storage encodings follow the pinned numerical prose's little-endian byte
order. Inputs of the generated width and well-formedness predicates are the
specified domain; the definitions also return values on other inputs. -/

namespace SpecExt.Builtins

def integerBytes : Nat → Nat → List byte
  | 0, _ => []
  | count + 1, value => .mk_byte (value % 256) :: integerBytes count (value / 256)

def integerOfBytes : List byte → Nat
  | [] => 0
  | .mk_byte value :: rest => value + 256 * integerOfBytes rest

end SpecExt.Builtins

def ibytes_ (v_N : N) (v_iN : iN) : List byte :=
  SpecExt.Builtins.integerBytes (v_N / 8) (proj_uN_0 v_iN)

def fbytes_ (v_N : N) (v_fN : fN) : List byte :=
  SpecExt.Builtins.integerBytes (v_N / 8) (SpecExt.Builtins.floatBits v_N v_fN)

def nbytes_ (v_numtype : numtype) (v_num_ : num_) : List byte :=
  match v_numtype, v_num_ with
  | .I32, .mk_num__0 _ value => ibytes_ 32 value
  | .I64, .mk_num__0 _ value => ibytes_ 64 value
  | .F32, .mk_num__1 _ value => fbytes_ 32 value
  | .F64, .mk_num__1 _ value => fbytes_ 64 value
  | _, _ => []

def vbytes_ (v_vectype : vectype) (v_vec_ : vec_) : List byte :=
  ibytes_ (vsize v_vectype) v_vec_

def inv_ibytes_ (_v_N : N) (var_0_lst : List byte) : iN :=
  .mk_uN (SpecExt.Builtins.integerOfBytes var_0_lst)

def inv_fbytes_ (v_N : N) (var_0_lst : List byte) : fN :=
  SpecExt.Builtins.floatOfBits v_N (SpecExt.Builtins.integerOfBytes var_0_lst)

def inv_nbytes_ (v_numtype : numtype) (var_0_lst : List byte) : num_ :=
  match v_numtype with
  | .I32 => .mk_num__0 .I32 (inv_ibytes_ 32 var_0_lst)
  | .I64 => .mk_num__0 .I64 (inv_ibytes_ 64 var_0_lst)
  | .F32 => .mk_num__1 .F32 (inv_fbytes_ 32 var_0_lst)
  | .F64 => .mk_num__1 .F64 (inv_fbytes_ 64 var_0_lst)

def inv_vbytes_ (v_vectype : vectype) (var_0_lst : List byte) : vec_ :=
  inv_ibytes_ (vsize v_vectype) var_0_lst
