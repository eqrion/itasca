import Itasca.Runtime.Code.Body.Reader.Common.ReaderEnterWasm2
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem reader_span_wasm2 {data env locals index st token next}
    (p : Wasm2.Pending data env .Wasm2 locals index st) (encoded : Wasm2.At data p.start token next) :
    st.core.pos.val ≤ next.val ∧ next.val ≤ data.length := by
  have span := encoded.span
  have pos := p.pos
  exact ⟨by omega, span.2⟩

theorem ReaderPostWasm2.span {data env locals index st out instruction poly values}
    {p : Wasm2.Pending data env .Wasm2 locals index st}
    (post : ReaderPostWasm2 p out instruction poly values) :
    st.core.pos.val ≤ out.pos.val ∧ out.pos.val ≤ data.length := reader_span_wasm2 p post.encoded

end Itasca.Runtime.Code
