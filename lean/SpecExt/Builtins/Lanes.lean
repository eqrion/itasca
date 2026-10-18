import SpecExt.Builtins.Bits

/-! Vector lanes follow the pinned numerical prose: lane zero occupies the
least significant bytes. Floating lanes preserve every bit, including NaN
payloads and signed zero. Well-formed shapes and lane lists are the specified
domain; these definitions are also total outside that domain. -/

namespace SpecExt.Builtins

def laneOfBits (ty : lanetype) (bits : Nat) : lane_ :=
  match ty with
  | .I8 => .mk_lane__0 .I8 (.mk_uN bits)
  | .I16 => .mk_lane__0 .I16 (.mk_uN bits)
  | .I32 => .mk_lane__0 .I32 (.mk_uN bits)
  | .I64 => .mk_lane__0 .I64 (.mk_uN bits)
  | .F32 => .mk_lane__1 .F32 (floatOfBits 32 bits)
  | .F64 => .mk_lane__1 .F64 (floatOfBits 64 bits)

def laneBits (ty : lanetype) : lane_ → Nat
  | .mk_lane__0 _ (.mk_uN bits) => bits
  | .mk_lane__1 _ value => floatBits (lsize ty) value

def unpackLanes (ty : lanetype) : Nat → Nat → List lane_
  | 0, _ => []
  | count + 1, bits =>
      laneOfBits ty (bits % 2 ^ lsize ty) :: unpackLanes ty count (bits / 2 ^ lsize ty)

def packLanes (ty : lanetype) : List lane_ → Nat
  | [] => 0
  | lane :: rest => laneBits ty lane + 2 ^ lsize ty * packLanes ty rest

theorem unpackLanes_length (ty : lanetype) (count bits : Nat) :
    (unpackLanes ty count bits).length = count := by
  induction count generalizing bits with
  | zero => rfl
  | succ count ih => simp only [unpackLanes, List.length_cons, ih]

end SpecExt.Builtins

def lanes_ (v_shape : shape) (v_vec_ : vec_) : List lane_ :=
  match v_shape with
  | .X ty (.mk_dim count) => SpecExt.Builtins.unpackLanes ty count (proj_uN_0 v_vec_)

def inv_lanes_ (v_shape : shape) (values : List lane_) : vec_ :=
  .mk_uN (SpecExt.Builtins.packLanes (fun_lanetype v_shape) values)
