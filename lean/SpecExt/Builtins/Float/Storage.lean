import SpecExt.Builtins.Float.Encoding
import SpecExt.Builtins.EncodingLemmas

/-! Bit-list and little-endian byte-list float roundtrips, including both zeros,
infinities, and all well-formed NaN payloads. -/

namespace SpecExt.Builtins.Float

theorem fbits_roundtrip_32 (value : fN) (h : wf_fN 32 value) :
    inv_fbits_ 32 (fbits_ 32 value) = value := by
  unfold inv_fbits_ fbits_
  rw [integerBits_roundtrip (floatBits_lt_32 value h)]
  exact float_roundtrip_32 value h

theorem fbits_roundtrip_64 (value : fN) (h : wf_fN 64 value) :
    inv_fbits_ 64 (fbits_ 64 value) = value := by
  unfold inv_fbits_ fbits_
  rw [integerBits_roundtrip (floatBits_lt_64 value h)]
  exact float_roundtrip_64 value h

theorem fbytes_roundtrip_32 (value : fN) (h : wf_fN 32 value) :
    inv_fbytes_ 32 (fbytes_ 32 value) = value := by
  change floatOfBits 32 (integerOfBytes (integerBytes 4 (floatBits 32 value))) = value
  have hb : floatBits 32 value < 256 ^ 4 := floatBits_lt_32 value h
  rw [integerBytes_roundtrip hb]
  exact float_roundtrip_32 value h

theorem fbytes_roundtrip_64 (value : fN) (h : wf_fN 64 value) :
    inv_fbytes_ 64 (fbytes_ 64 value) = value := by
  change floatOfBits 64 (integerOfBytes (integerBytes 8 (floatBits 64 value))) = value
  have hb : floatBits 64 value < 256 ^ 8 := floatBits_lt_64 value h
  rw [integerBytes_roundtrip hb]
  exact float_roundtrip_64 value h

end SpecExt.Builtins.Float
