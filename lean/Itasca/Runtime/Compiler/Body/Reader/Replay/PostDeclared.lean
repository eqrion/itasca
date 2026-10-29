import Itasca.Runtime.Compiler.Body.Reader.Replay.Post
import Itasca.Binary.Wasm2.EncodingUnique

/-!
Exact byte provenance identifies the retained instruction with the canonical accepted trace, so declared-reference evidence is recovered from the reader.

Main declarations: `ReaderPostWasm2.declared`. A direct consumer is `Compiler.Body.Reader.Replay.IndexedStateful`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Exact byte provenance identifies the retained instruction with the canonical
accepted trace, so declared-reference evidence is recovered from the reader. -/
theorem ReaderPostWasm2.declared {data env locals index st out instruction poly values}
    {p : Wasm2.Pending data env .Wasm2 locals index st}
    (post : ReaderPostWasm2 p out instruction poly values) :
    DeclaredReferences.Instruction (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) instruction := by
  have consumed := Wasm2.Consumed.snoc p.consumed post.encoded
  have all : Wasm2.TokensDeclared (env.declared_funcs.val.map (fun i => uN.mk_uN i.val))
      (Wasm2.Frames.trace p.parents p.current ++ [.plain instruction]) := by
    cases post.after.1 with
    | running ft parents current signature bounds opened bodyType canonical declared =>
      rw [consumed.unique canonical]
      exact declared
    | closed ft ops tokens signature bounds controls blocks body typed canonical declared =>
      rw [consumed.unique canonical]
      exact declared
  simpa only [Wasm2.tokensDeclared_singleton,Wasm2.Token.Declared] using
    ((Wasm2.tokensDeclared_append _ _ _).mp all).2

end Itasca.Runtime.Compiler
