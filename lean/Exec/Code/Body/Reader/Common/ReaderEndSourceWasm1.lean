import Exec.Code.Body.Reader.Control.ReaderPrefixElseEnteredWasm1
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Every retained Wasm 1 scope signature is the literal source block signature. -/
theorem SourceScopeMatchesWasm1.signature {scope saved}
    (same : SourceScopeMatchesWasm1 scope saved) (types : List functype) :
    BlockSignature types (Control.blockType saved.ctrl.block_type) scope.params scope.results := by
  rw [same.params, same.results]
  cases saved.ctrl.block_type <;> constructor

/-- The closing source constructor uses exactly the matched literal block type. -/
theorem SourceScopeMatchesWasm1.close_form {scope saved instruction}
    (same : SourceScopeMatchesWasm1 scope saved)
    (closed : Wasm1.Frames.Closed saved.form saved.ctrl.block_type saved.ops instruction) :
    (scope.form = .block (Control.blockType saved.ctrl.block_type) ∧
      instruction = .BLOCK (Control.blockType saved.ctrl.block_type) scope.source) ∨
    (scope.form = .loop (Control.blockType saved.ctrl.block_type) ∧
      instruction = .LOOP (Control.blockType saved.ctrl.block_type) scope.source) ∨
    (∃ condition, scope.form = .then_ (Control.blockType saved.ctrl.block_type) condition ∧
      instruction = .IFELSE (Control.blockType saved.ctrl.block_type) scope.source [] ∧
      scope.params = scope.results) ∨
    (∃ condition yes noEntry yesExit yesNormal,
      scope.form = .else_ (Control.blockType saved.ctrl.block_type) condition yes yesExit noEntry yesNormal ∧
      instruction = .IFELSE (Control.blockType saved.ctrl.block_type) yes scope.source) := by
  obtain ⟨matched, params, results, source⟩ := same
  generalize hf : saved.form = form at closed matched
  generalize ht : saved.ctrl.block_type = bt at closed matched results
  generalize hs : saved.ops = body at closed source
  generalize sf : scope.form = current at matched
  cases closed <;> cases matched
  · exact .inl ⟨rfl, by rw [source]⟩
  · exact .inr (.inl ⟨rfl, by rw [source]⟩)
  · exact .inr (.inr (.inl ⟨_, rfl, by rw [source], by simpa [Control.resultTypes] using params.trans results.symm⟩))
  · exact .inr (.inr (.inr ⟨_, _, _, _, _, rfl, by rw [source]⟩))
end Exec.Code
