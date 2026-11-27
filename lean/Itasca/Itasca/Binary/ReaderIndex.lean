import Itasca.Binary.LebReaders
import Itasca.Binary.LebBytes

namespace Itasca.Binary.Source
open Aeneas.Std

theorem readerLeb {bs n} (h : WebAssembly.Binary.Leb128.U32Encoding bs n) :
    Leb128.Encoding (readerBytes bs) n := (Leb128.encoding_iff _ _).mpr (by simpa only [bytes_readerBytes] using h)

theorem readerIndex {bs n} (h : WebAssembly.Binary.Leb128.U32Encoding bs n) :
    ∃ i : U32, i.val = n ∧ IndexEncoding i (readerBytes bs) := by
  have e := readerLeb h
  exact ⟨U32.ofNatCore n e.value_lt, rfl, e⟩

end Itasca.Binary.Source
