import Itasca.Runtime.Code.Local.Control.Common.CumulativeMiscSupport
namespace Itasca.Wasm2
open Aeneas Aeneas.Std

/-- The complete independent body encoding determines every accepted misc
subopcode without an additional source-subset premise. -/
theorem BodyEncoding.next_misc {data body tokens position}
    (encoded : BodyEncoding data body)
    (before : Consumed data 0#usize tokens position) (remaining : position.val < data.length)
    (next : Usize) (advance : next.val = position.val + 1)
    (byte : data.val[position.val]'remaining = 252#u8) :
    ∃ subopcode endPosition, Leb128.Decoded data next subopcode endPosition ∧
      Itasca.Runtime.Code.CumulativeMiscOpcode subopcode := by
  obtain ⟨allTokens,finish,complete,endPosition,spelling⟩ := encoded
  obtain ⟨token,nextToken,suffix,split,atToken,rest⟩ := before.next_of_prefix complete (by omega)
  exact atToken.cumulative_misc next advance remaining byte
end Itasca.Wasm2
