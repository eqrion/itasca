import SpecExt.Builtins.Bytes
import SpecExt.Builtins.Int
import SpecExt.Builtins.Lanes
import SpecExt.Builtins.Misc

/-! Kernel-checked integer vectors: signed boundaries, masked shift counts,
MSB-first bits, saturation, and Q15's exceptional minimum-times-minimum case.
No evaluation bypasses the kernel. Floating-point examples belong to M7. -/

namespace SpecExt.Builtins.Examples

example : lanes_ (.X .I64 (.mk_dim 2)) (.mk_uN 18446744073709551617) =
    [.mk_lane__0 .I64 (.mk_uN 1), .mk_lane__0 .I64 (.mk_uN 1)] := by decide
example : inv_lanes_ (.X .I32 (.mk_dim 4))
    [.mk_lane__0 .I32 (.mk_uN 1), .mk_lane__0 .I32 (.mk_uN 2),
     .mk_lane__0 .I32 (.mk_uN 3), .mk_lane__0 .I32 (.mk_uN 4)] =
    .mk_uN 316912650112397582603894390785 := by decide
example : lanes_ (.X .F64 (.mk_dim 2)) (.mk_uN 9223372036854775808) =
    [.mk_lane__1 .F64 (.NEG (.SUBNORM 0)),
     .mk_lane__1 .F64 (.POS (.SUBNORM 0))] := by decide

example : ibits_ 8 (.mk_uN 129) =
    [.mk_bit 1, .mk_bit 0, .mk_bit 0, .mk_bit 0,
     .mk_bit 0, .mk_bit 0, .mk_bit 0, .mk_bit 1] := by decide
example : inv_ibits_ 4 [.mk_bit 1, .mk_bit 0, .mk_bit 1, .mk_bit 0] = .mk_uN 10 := by decide
example : s33_to_u32 (.mk_sN 4294967295) = .mk_uN 4294967295 := by decide
example : truncz (Rat.mk' (-7) 2) = -3 := by decide
example : truncz (Rat.mk' 7 2) = 3 := by decide
example : truncz (Rat.mk' (-1) 2) = 0 := by decide
example : extend__ 8 32 .S (.mk_uN 128) = .mk_uN 4294967168 := by decide
example : extend__ 8 32 .S (.mk_uN 127) = .mk_uN 127 := by decide
example : extend__ 8 32 .U (.mk_uN 255) = .mk_uN 255 := by decide
example : wrap__ 64 32 (.mk_uN 4294967297) = .mk_uN 1 := by decide
example : narrow__ 16 8 .S (.mk_uN 256) = .mk_uN 127 := by decide
example : narrow__ 16 8 .S (.mk_uN 65280) = .mk_uN 128 := by decide
example : narrow__ 16 8 .U (.mk_uN 65535) = .mk_uN 0 := by decide
example : narrow__ 16 8 .U (.mk_uN 256) = .mk_uN 255 := by decide
example : narrow__ 16 8 .U (.mk_uN 127) = .mk_uN 127 := by decide
example : iclz_ 32 (.mk_uN 0) = .mk_uN 32 := by decide
example : ictz_ 64 (.mk_uN 0) = .mk_uN 64 := by decide
example : iclz_ 32 (.mk_uN 1) = .mk_uN 31 := by decide
example : ictz_ 32 (.mk_uN 2147483648) = .mk_uN 31 := by decide
example : ipopcnt_ 64 (.mk_uN 18446744073709551615) = .mk_uN 64 := by decide
example : iand_ 8 (.mk_uN 170) (.mk_uN 204) = .mk_uN 136 := by decide
example : ior_ 8 (.mk_uN 170) (.mk_uN 204) = .mk_uN 238 := by decide
example : ixor_ 8 (.mk_uN 170) (.mk_uN 204) = .mk_uN 102 := by decide
example : inot_ 8 (.mk_uN 170) = .mk_uN 85 := by decide
example : irev_ 8 (.mk_uN 19) = .mk_uN 200 := by decide
example : iandnot_ 8 (.mk_uN 170) (.mk_uN 204) = .mk_uN 34 := by decide
example : ibitselect_ 8 (.mk_uN 170) (.mk_uN 85) (.mk_uN 15) = .mk_uN 90 := by decide
example : ishl_ 32 (.mk_uN 2147483649) (.mk_uN 33) = .mk_uN 2 := by decide
example : ishr_ 32 .S (.mk_uN 4294967293) (.mk_uN 1) = .mk_uN 4294967294 := by decide
example : ishr_ 32 .U (.mk_uN 4294967293) (.mk_uN 1) = .mk_uN 2147483646 := by decide
example : ishr_ 64 .S (.mk_uN 9223372036854775808) (.mk_uN 64) =
    .mk_uN 9223372036854775808 := by decide
example : irotl_ 8 (.mk_uN 129) (.mk_uN 9) = .mk_uN 3 := by decide
example : irotr_ 8 (.mk_uN 129) (.mk_uN 9) = .mk_uN 192 := by decide
example : iavgr_ 8 .U (.mk_uN 0) (.mk_uN 1) = .mk_uN 1 := by decide
example : iavgr_ 8 .U (.mk_uN 255) (.mk_uN 255) = .mk_uN 255 := by decide
example : iq15mulr_sat_ 16 .S (.mk_uN 32768) (.mk_uN 32768) = .mk_uN 32767 := by decide
example : iq15mulr_sat_ 16 .S (.mk_uN 16384) (.mk_uN 16384) = .mk_uN 8192 := by decide
example : iq15mulr_sat_ 16 .S (.mk_uN 32768) (.mk_uN 32767) = .mk_uN 32769 := by decide
example : iq15mulr_sat_ 16 .S (.mk_uN 65535) (.mk_uN 16384) = .mk_uN 0 := by decide
example : inv_concat_ Nat [1, 2, 3, 4] = [[1, 2], [3, 4]] := by decide
example : inv_concat_ Nat [] = [] := by decide

end SpecExt.Builtins.Examples

-- The byte order differs from the bit-list order. These vectors include sign,
-- exponent and payload preservation, rather than only finite positive values.
example : ibytes_ 32 (.mk_uN 0x12345678) = [.mk_byte 0x78, .mk_byte 0x56, .mk_byte 0x34, .mk_byte 0x12] := by decide
example : inv_ibytes_ 32 [.mk_byte 0x78, .mk_byte 0x56, .mk_byte 0x34, .mk_byte 0x12] = .mk_uN 0x12345678 := by decide
example : fbytes_ 32 (.NEG (.SUBNORM 0)) = [.mk_byte 0, .mk_byte 0, .mk_byte 0, .mk_byte 128] := by decide
example : inv_fbytes_ 32 [.mk_byte 0, .mk_byte 0, .mk_byte 128, .mk_byte 63] = .POS (.NORM 0 0) := by decide
example : inv_fbytes_ 32 [.mk_byte 1, .mk_byte 0, .mk_byte 128, .mk_byte 127] = .POS (.NAN 1) := by decide
example : SpecExt.Builtins.floatBits 64 (.NEG (.NORM 0 0)) = 0xbff0000000000000 := by decide
example : SpecExt.Builtins.floatOfBits 64 0x7ff0000000000000 = .POS .INF := by decide
example : SpecExt.Builtins.floatOfBits 64 1 = .POS (.SUBNORM 1) := by decide
example : inv_nbytes_ .I32 (nbytes_ .I32 (.mk_num__0 .I32 (.mk_uN 0x12345678))) = .mk_num__0 .I32 (.mk_uN 0x12345678) := by decide
example : inv_vbytes_ .V128 (vbytes_ .V128 (.mk_uN 0x123456789abcdef0123456789abcdef0)) = .mk_uN 0x123456789abcdef0123456789abcdef0 := by decide
