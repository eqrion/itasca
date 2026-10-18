import SpecExt.Builtins.Float.Lemmas

/-! IEEE boundary vectors checked by kernel reduction, with no native evaluator.
The specification uses exact rationals and integer square comparisons. -/

namespace SpecExt.Builtins.Float.Examples
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private def f32 (bits : Nat) : fN := floatOfBits 32 bits
private def f64 (bits : Nat) : fN := floatOfBits 64 bits

example : fadd_ 32 (f32 0x3f800000) (f32 0x40000000) = [f32 0x40400000] := by decide +kernel
example : fadd_ 32 (f32 0x3f800000) (f32 0x33800000) = [f32 0x3f800000] := by decide +kernel
example : fadd_ 32 (f32 0x3f800001) (f32 0x33800000) = [f32 0x3f800002] := by decide +kernel
example : fadd_ 32 (f32 0x80000000) (f32 0x80000000) = [f32 0x80000000] := by decide +kernel
example : fadd_ 32 (f32 0x80000000) (f32 0) = [f32 0] := by decide +kernel
example : fsub_ 32 (f32 0x3f800000) (f32 0x3f800000) = [f32 0] := by decide +kernel
example : fmul_ 32 (f32 0x7f7fffff) (f32 0x40000000) = [f32 0x7f800000] := by decide +kernel
example : fmul_ 32 (f32 1) (f32 0x3f000000) = [f32 0] := by decide +kernel
example : fmul_ 32 (f32 3) (f32 0x3f000000) = [f32 2] := by decide +kernel
example : fdiv_ 32 (f32 0xbf800000) (f32 0x7f800000) = [f32 0x80000000] := by decide +kernel
example : fsqrt_ 32 (f32 0x40800000) = [f32 0x40000000] := by decide +kernel
example : fsqrt_ 32 (f32 0x40000000) = [f32 0x3fb504f3] := by decide +kernel
example : fsqrt_ 32 (f32 0x80000000) = [f32 0x80000000] := by decide +kernel
example : fceil_ 32 (f32 0xbf000000) = [f32 0x80000000] := by decide +kernel
example : ffloor_ 32 (f32 0xbf000000) = [f32 0xbf800000] := by decide +kernel
example : fnearest_ 32 (f32 0x40200000) = [f32 0x40000000] := by decide +kernel
example : fnearest_ 32 (f32 0xc0600000) = [f32 0xc0800000] := by decide +kernel
example : feq_ 32 (f32 0x7fc00000) (f32 0x7fc00000) = .mk_uN 0 := by decide +kernel
example : feq_ 32 (f32 0) (f32 0x80000000) = .mk_uN 1 := by decide +kernel
example : flt_ 32 (f32 0xff800000) (f32 0xbf800000) = .mk_uN 1 := by decide +kernel
example : fmin_ 32 (f32 0) (f32 0x80000000) = [f32 0x80000000] := by decide +kernel
example : fmax_ 32 (f32 0) (f32 0x80000000) = [f32 0] := by decide +kernel
example : fpmin_ 32 (f32 0x7f800001) (f32 0x3f800000) = [f32 0x7f800001] := by decide +kernel
example : promote__ 32 64 (f32 1) = [f64 0x36a0000000000000] := by decide +kernel
example : demote__ 64 32 (f64 0x3ff0000010000000) = [f32 0x3f800000] := by decide +kernel
example : convert__ 32 32 .U (.mk_uN 16777217) = f32 0x4b800000 := by decide +kernel
example : trunc__ 32 32 .S (f32 0xcf000000) = some (.mk_uN 2147483648) := by decide +kernel
example : trunc__ 32 32 .S (f32 0x4f000000) = none := by decide +kernel
example : trunc_sat__ 32 32 .U (f32 0x7f800000) = some (.mk_uN 4294967295) := by decide +kernel
example : trunc_sat__ 32 32 .S (f32 0xff800000) = some (.mk_uN 2147483648) := by decide +kernel
example : trunc_sat__ 32 32 .S (f32 0x7fc00000) = some (.mk_uN 0) := by decide +kernel

end SpecExt.Builtins.Float.Examples
