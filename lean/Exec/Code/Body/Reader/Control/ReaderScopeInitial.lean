import Exec.Code.Body.Reader.Control.ReaderScopeZipper
import Exec.Code.Local.Callbacks.Control.ScopeFrame
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

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
