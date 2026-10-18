import Exec.Code.Body.Reader.Control.ReaderScopeZipper
import Exec.Code.Local.Callbacks.Control.ScopeFrame
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- The compiler's empty root scope matches the validator's fresh body frame. -/
theorem ReaderScopeZipperWasm1.initial (bt : code.BlockType) (state : code.OpIterState) :
    ReaderScopeZipperWasm1 [] (SourceScope.initial (Control.resultTypes bt)) []
      (Wasm1.Frames.Saved.fresh state .body bt) := by
  refine ⟨.nil, ?_⟩
  constructor
  · exact .body
  · rfl
  · rfl
  · rfl

theorem ReaderScopeZipperWasm2.initial (bt : signature.BlockType) (base : Usize)
    (ins outs : List types.ValueType) :
    ReaderScopeZipperWasm2 [] (SourceScope.initial (outs.map Translate.valueType)) []
      (Wasm2.Frames.Saved.fresh base .body bt ins outs) := by
  refine ⟨.nil, ?_⟩
  constructor
  · exact .body
  · rfl
  · rfl
  · rfl
end Exec.Code
