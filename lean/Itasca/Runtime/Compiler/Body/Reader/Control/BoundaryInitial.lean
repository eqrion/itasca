import Itasca.Runtime.Compiler.Body.Reader.Control.Boundary
import Itasca.Wasm2.Invariant

/-!
The initial reader boundary before body compilation.

Main declarations: `ReaderBoundaryWasm2.initial`. A direct consumer is `Compiler.Body.Reader.Replay.IndexedCompilerInitial`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem ReaderBoundaryWasm2.initial (data : Slice U8) (env : metadata.Env)
    (locals : alloc.vec.Vec wasm_types.ValueType) (index : U32) (ft : wasm_types.FuncType)
    (signature : env.types.val[index.val]? = some ft)
    (size : data.length ≤ limits.MAX_FUNCTION_BYTES.val) :
    ReaderBoundaryWasm2 data env locals index ft (Wasm2.initial index) []
      (Wasm2.Frames.Saved.fresh 0#usize .body (.TypeIndex index) ft.params.val ft.results.val) := by
  refine ⟨signature, ?_, ?_, rfl, ?_, ?_⟩
  · constructor <;> simp [Wasm2.initial, size]
  · apply Wasm2.Frames.Open.start env _ (EnvTranslation.context_wf env ⟨locals, ft.results⟩)
    · simp [Wasm2.resolve, Wasm2.inputs, signature]
    · simp [Wasm2.resolve, Wasm2.outputs, signature]
    · rfl
    · rfl
    · rfl
  · simpa [Wasm2.Frames.trace, Wasm2.Frames.Saved.trace, Wasm2.Frames.Saved.fresh,
      Wasm2.Frames.Form.opening, Wasm2.initial] using Wasm2.Consumed.nil (data := data) 0#usize (by simp)
  · simp [Wasm2.Frames.trace, Wasm2.Frames.Saved.trace, Wasm2.Frames.Saved.fresh, Wasm2.Frames.Form.opening]
end Itasca.Runtime.Compiler
