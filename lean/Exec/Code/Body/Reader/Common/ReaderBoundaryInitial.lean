import Exec.Code.Body.Reader.Common.ReaderBoundary
import Itasca.Wasm1.Run
import Itasca.Wasm2.Invariant
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- The initial canonical boundary fixes the fresh root witness before any
opcode is consumed. -/
theorem ReaderBoundaryWasm1.initial (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (bt : code.BlockType) (size : data.length ≤ limits.MAX_FUNCTION_BYTES.val) :
    ReaderBoundaryWasm1 data env ctx bt (Wasm1.Loop.initial bt) []
      (Wasm1.Frames.Saved.fresh (Wasm1.Loop.initial bt) .body bt) := by
  refine ⟨?_, ?_, rfl, ?_⟩
  · constructor <;> simp [Wasm1.Loop.initial, size]
  · apply Wasm1.Frames.Open.start _ (EnvTranslation.context_wf env ctx) <;> rfl
  · simpa [Wasm1.Frames.trace, Wasm1.Frames.Saved.trace, Wasm1.Frames.Saved.fresh,
      Wasm1.Frames.Form.opening, Wasm1.Loop.initial] using
      Wasm1.Consumed.nil (data := data) 0#usize (by simp)

theorem ReaderBoundaryWasm2.initial (data : Slice U8) (env : module.Env)
    (locals : alloc.vec.Vec types.ValueType) (index : U32) (ft : types.FuncType)
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
end Exec.Code
