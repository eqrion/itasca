import Itasca.Binary.Wasm1.EncodingUnique
import Itasca.Binary.Wasm2.EncodingUnique
import Exec.Code.Body.Reader.Common.ReaderBoundary
import Exec.Code.Body.Reader.Common.ReaderEnterWasm1
import Exec.Code.Body.Reader.Common.ReaderEnterWasm2
import Exec.Code.Body.Reader.Common.ReaderCloseWasm1
import Exec.Code.Body.Reader.Common.ReaderCloseWasm2
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem ReaderEnterPostWasm1.boundary {data env ctx bodyBt st out form bt remaining token}
    {p : Wasm1.Pending data env ctx bodyBt st}
    (post : ReaderEnterPostWasm1 p out form bt remaining token)
    (opening : form.opening bt = [token]) :
    ReaderBoundaryWasm1 data env ctx bodyBt out
      (p.parents ++ [{p.current with vals := remaining}])
      (Wasm1.Frames.Saved.fresh out form bt) := by
  refine ⟨post.after.1.bounds, post.opened, ?_, ?_⟩
  · simpa only [Wasm1.Frames.bodyType_enter] using p.bodyType
  · have consumed := Wasm1.Consumed.snoc p.consumed post.encoded
    simpa [Wasm1.Frames.trace, Wasm1.Frames.Saved.trace, Wasm1.Frames.Saved.fresh,
      Control.frame, opening, List.append_assoc] using consumed

theorem ReaderEnterPostWasm2.boundary {data env locals index st out form bt ins outs remaining base}
    {p : Wasm2.Pending data env locals index st}
    (post : ReaderEnterPostWasm2 p out form bt ins outs remaining base)
    (initial : form.Initial) :
    ReaderBoundaryWasm2 data env locals index p.ft out
      (p.parents ++ [{p.current with vals := remaining}])
      (Wasm2.Frames.Saved.fresh base form bt ins outs) := by
  have opening : form.opening bt = [form.token bt] := by
    rcases initial with rfl | rfl | rfl <;> rfl
  have trace : Wasm2.Frames.trace (p.parents ++ [{p.current with vals := remaining}])
      (Wasm2.Frames.Saved.fresh base form bt ins outs) =
      Wasm2.Frames.trace p.parents p.current ++ [form.token bt] := by
    simp [Wasm2.Frames.trace, Wasm2.Frames.Saved.trace, Wasm2.Frames.Saved.fresh,
      opening, List.append_assoc]
  refine ⟨p.signature, post.after.1.bounds, post.opened, ?_, ?_, ?_⟩
  · simpa only [Wasm2.Frames.bodyType_enter] using p.bodyType
  · rw [trace]; exact Wasm2.Consumed.snoc p.consumed post.encoded
  · rw [trace, Wasm2.tokensDeclared_append, Wasm2.tokensDeclared_singleton]
    exact ⟨p.declared, by cases form <;> simp [Wasm2.Frames.Form.token, Wasm2.Token.Declared]⟩

theorem reader_else_boundary_wasm1 {data env ctx bt st out}
    (p : Wasm1.Pending data env ctx bt st)
    (form : p.current.form = .then_)
    (encoded : Wasm1.At data p.start .else_ out.pos)
    (opened : Wasm1.Frames.Open (EnvTranslation.context env ctx) out p.parents p.current.nextElse)
    (after : p.After out) :
    ReaderBoundaryWasm1 data env ctx bt out p.parents p.current.nextElse := by
  refine ⟨after.1.bounds, opened, ?_, ?_⟩
  · simpa only [Wasm1.Frames.bodyType_else] using p.bodyType
  · have consumed := Wasm1.Consumed.snoc p.consumed encoded
    simpa [Wasm1.Frames.trace, Wasm1.Frames.Saved.trace, Wasm1.Frames.Saved.nextElse,
      form, Wasm1.Frames.Form.opening, List.append_assoc] using consumed

theorem reader_else_boundary_wasm2 {data env locals index st out}
    (p : Wasm2.Pending data env locals index st)
    (form : p.current.form = .then_)
    (encoded : Wasm2.At data p.start .else_ out.core.pos)
    (opened : Wasm2.Frames.Open env (Wasm2.bodyContext env locals p.ft) out p.parents p.current.nextElse)
    (after : p.After out) :
    ReaderBoundaryWasm2 data env locals index p.ft out p.parents p.current.nextElse := by
  have trace : Wasm2.Frames.trace p.parents p.current.nextElse =
      Wasm2.Frames.trace p.parents p.current ++ [.else_] := by
    simp [Wasm2.Frames.trace, Wasm2.Frames.Saved.trace, Wasm2.Frames.Saved.nextElse,
      form, Wasm2.Frames.Form.opening, List.append_assoc]
  refine ⟨p.signature, after.1.bounds, opened, ?_, ?_, ?_⟩
  · simpa only [Wasm2.Frames.bodyType_else] using p.bodyType
  · rw [trace]; exact Wasm2.Consumed.snoc p.consumed encoded
  · rw [trace, Wasm2.tokensDeclared_append, Wasm2.tokensDeclared_singleton]
    exact ⟨p.declared, trivial⟩

theorem reader_end_boundary_wasm1 {data env ctx bt st out grandparents parent instruction}
    (p : Wasm1.Pending data env ctx bt st)
    (parents : p.parents = grandparents ++ [parent])
    (encoded : Wasm1.At data p.start .end_ out.pos)
    (opened : Wasm1.Frames.Open (EnvTranslation.context env ctx) out grandparents
      (resumedSourceWasm1 parent p.current instruction)) (after : p.After out) :
    ReaderBoundaryWasm1 data env ctx bt out grandparents
      (resumedSourceWasm1 parent p.current instruction) := by
  refine ⟨after.1.bounds, opened, ?_, ?_⟩
  · exact (Wasm1.Frames.bodyType_close grandparents parent p.current instruction).trans
      (by simpa only [← parents] using p.bodyType)
  · have consumed := Wasm1.Consumed.snoc p.consumed encoded
    simpa [Wasm1.Frames.trace, Wasm1.Frames.Saved.trace, resumedSourceWasm1,
      parents, List.append_assoc] using consumed

theorem reader_end_boundary_wasm2 {data env locals index st out grandparents parent instruction}
    (p : Wasm2.Pending data env locals index st)
    (parents : p.parents = grandparents ++ [parent])
    (encoded : Wasm2.At data p.start .end_ out.core.pos)
    (opened : Wasm2.Frames.Open env (Wasm2.bodyContext env locals p.ft) out grandparents
      (resumedSource parent p.current instruction)) (after : p.After out) :
    ReaderBoundaryWasm2 data env locals index p.ft out grandparents
      (resumedSource parent p.current instruction) := by
  have trace : Wasm2.Frames.trace grandparents (resumedSource parent p.current instruction) =
      Wasm2.Frames.trace p.parents p.current ++ [.end_] := by
    simp [Wasm2.Frames.trace, Wasm2.Frames.Saved.trace, resumedSource, parents, List.append_assoc]
  refine ⟨p.signature, after.1.bounds, opened, ?_, ?_, ?_⟩
  · exact (Wasm2.Frames.bodyType_close grandparents parent p.current instruction).trans
      (by simpa only [← parents] using p.bodyType)
  · rw [trace]; exact Wasm2.Consumed.snoc p.consumed encoded
  · rw [trace, Wasm2.tokensDeclared_append, Wasm2.tokensDeclared_singleton]
    exact ⟨p.declared, trivial⟩

/-- Root END identifies the exact accumulated body, without selecting a fresh
existential source program from the general validator invariant. -/
theorem reader_root_end_encoding_wasm1 {data env ctx bt st out}
    (p : Wasm1.Pending data env ctx bt st)
    (root : p.current.form = .body)
    (encoded : Wasm1.At data p.start .end_ out.pos)
    (zipper : ReaderEndZipperWasm1 p out)
    (finished : out.pos.val = data.length) :
    Wasm1.BodyEncoding data p.current.ops := by
  rcases zipper with ⟨_, _, tokens, _⟩ | ⟨_, _, _, _, closed, _⟩
  · exact ⟨_, out.pos, Wasm1.Consumed.snoc p.consumed encoded, finished, tokens⟩
  · exact False.elim (closed.not_body root)

theorem reader_root_end_encoding_wasm2 {data env locals index st out}
    (p : Wasm2.Pending data env locals index st)
    (root : p.current.form = .body)
    (encoded : Wasm2.At data p.start .end_ out.core.pos)
    (zipper : ReaderEndZipper p out)
    (finished : out.core.pos.val = data.length) :
    Wasm2.BodyEncoding data p.current.ops := by
  rcases zipper with ⟨_, _, tokens, _⟩ | ⟨_, _, _, _, closed, _⟩
  · exact ⟨_, out.core.pos, Wasm2.Consumed.snoc p.consumed encoded, finished, tokens⟩
  · have notBody : ∀ {form bt ops instruction},
        Wasm2.Frames.Closed form bt ops instruction → form ≠ .body := by
      intro form bt ops instruction closed
      cases closed <;> simp
    exact False.elim (notBody closed root)

theorem reader_root_end_source_wasm1 {data env ctx bt st out source}
    (p : Wasm1.Pending data env ctx bt st)
    (root : p.current.form = .body)
    (encoded : Wasm1.At data p.start .end_ out.pos)
    (zipper : ReaderEndZipperWasm1 p out)
    (finished : out.pos.val = data.length)
    (body : Wasm1.BodyEncoding data source) : p.current.ops = source :=
  (reader_root_end_encoding_wasm1 p root encoded zipper finished).unique body

theorem reader_root_end_source_wasm2 {data env locals index st out source}
    (p : Wasm2.Pending data env locals index st)
    (root : p.current.form = .body)
    (encoded : Wasm2.At data p.start .end_ out.core.pos)
    (zipper : ReaderEndZipper p out)
    (finished : out.core.pos.val = data.length)
    (body : Wasm2.BodyEncoding data source) : p.current.ops = source :=
  (reader_root_end_encoding_wasm2 p root encoded zipper finished).unique body
end Exec.Code
