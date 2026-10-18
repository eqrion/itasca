import Exec.Code.Body.Reader.Common.ReaderEnterWasm1
import Exec.Code.Body.Reader.Common.ReaderEnterWasm2
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- The source token includes the already-fetched opcode and never moves the reader backwards. -/
theorem reader_span_wasm1 {data env ctx bt st token next}
    (p : Wasm1.Pending data env ctx bt st) (encoded : Wasm1.At data p.start token next) :
    st.pos.val ≤ next.val ∧ next.val ≤ data.length := by
  have span := encoded.span
  have pos := p.pos
  exact ⟨by omega, span.2⟩

theorem reader_span_wasm2 {data env locals index st token next}
    (p : Wasm2.Pending data env locals index st) (encoded : Wasm2.At data p.start token next) :
    st.core.pos.val ≤ next.val ∧ next.val ≤ data.length := by
  have span := encoded.span
  have pos := p.pos
  exact ⟨by omega, span.2⟩

theorem ReaderPostWasm1.span {data env ctx bt st out instruction poly values}
    {p : Wasm1.Pending data env ctx bt st}
    (post : ReaderPostWasm1 p out instruction poly values) :
    st.pos.val ≤ out.pos.val ∧ out.pos.val ≤ data.length := reader_span_wasm1 p post.encoded

theorem ReaderPostWasm2.span {data env locals index st out instruction poly values}
    {p : Wasm2.Pending data env locals index st}
    (post : ReaderPostWasm2 p out instruction poly values) :
    st.core.pos.val ≤ out.pos.val ∧ out.pos.val ≤ data.length := reader_span_wasm2 p post.encoded

theorem ReaderEnterPostWasm1.span {data env ctx bt st out form signature remaining token}
    {p : Wasm1.Pending data env ctx bt st}
    (post : ReaderEnterPostWasm1 p out form signature remaining token) :
    st.pos.val ≤ out.pos.val ∧ out.pos.val ≤ data.length := reader_span_wasm1 p post.encoded

theorem ReaderEnterPostWasm2.span {data env locals index st out form signature ins outs remaining base}
    {p : Wasm2.Pending data env locals index st}
    (post : ReaderEnterPostWasm2 p out form signature ins outs remaining base) :
    st.core.pos.val ≤ out.core.pos.val ∧ out.core.pos.val ≤ data.length := reader_span_wasm2 p post.encoded
end Exec.Code
