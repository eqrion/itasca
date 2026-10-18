import Exec.Code.Body.Reader.Control.ReaderScopeWasm2
import Exec.Code.Local.Control.Common.Structured
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem reader_block_signature_wasm2 (env : module.Env) (bt : signature.BlockType)
    (ins outs : List types.ValueType)
    (inputs : Wasm2.resolve env (Wasm2.inputs bt) = some ins)
    (outputs : Wasm2.resolve env (Wasm2.outputs bt) = some outs) :
    BlockSignature (env.types.val.map EnvTranslation.funcType) (Wasm2.blockType bt)
      (ins.map Translate.valueType) (outs.map Translate.valueType) := by
  cases bt with
  | Empty =>
    simp [Wasm2.inputs, Wasm2.outputs, Wasm2.resolve] at inputs outputs
    subst ins; subst outs
    exact .empty
  | Value t =>
    simp [Wasm2.inputs, Wasm2.outputs, Wasm2.resolve] at inputs outputs
    subst ins; subst outs
    exact .value _
  | TypeIndex i =>
    by_cases bound : i.val < env.types.val.length
    · simp [Wasm2.inputs, Wasm2.outputs, Wasm2.resolve, List.getElem?_eq_getElem bound] at inputs outputs
      subst ins; subst outs
      apply BlockSignature.index
      simp [List.getElem?_eq_getElem bound, EnvTranslation.funcType]
    · simp [Wasm2.inputs, Wasm2.resolve, List.getElem?_eq_none (by omega : env.types.val.length ≤ i.val)] at inputs

theorem SourceScopeMatchesWasm2.signature {scope saved}
    (same : SourceScopeMatchesWasm2 scope saved) (env : module.Env)
    (nonBody : saved.form ≠ .body)
    (inputs : Wasm2.resolve env (Wasm2.inputs saved.bt) = some saved.ins)
    (outputs : Wasm2.resolve env (Wasm2.outputs saved.bt) = some saved.outs) :
    BlockSignature (env.types.val.map EnvTranslation.funcType) (Wasm2.blockType saved.bt) scope.params scope.results := by
  rw [same.params, same.results]
  have params : saved.form.params saved.ins = saved.ins := by cases form : saved.form <;> simp_all [Wasm2.Frames.Form.params]
  rw [params]
  exact reader_block_signature_wasm2 env saved.bt saved.ins saved.outs inputs outputs

theorem SourceScopeMatchesWasm2.close_form {scope saved instruction}
    (same : SourceScopeMatchesWasm2 scope saved)
    (closed : Wasm2.Frames.Closed saved.form saved.bt saved.ops instruction)
    (identity : saved.form = .then_ → saved.ins = saved.outs) :
    (scope.form = .block (Wasm2.blockType saved.bt) ∧
      instruction = .BLOCK (Wasm2.blockType saved.bt) scope.source) ∨
    (scope.form = .loop (Wasm2.blockType saved.bt) ∧
      instruction = .LOOP (Wasm2.blockType saved.bt) scope.source) ∨
    (∃ condition, scope.form = .then_ (Wasm2.blockType saved.bt) condition ∧
      instruction = .IFELSE (Wasm2.blockType saved.bt) scope.source [] ∧
      scope.params = scope.results) ∨
    (∃ condition yes noEntry yesExit yesNormal,
      scope.form = .else_ (Wasm2.blockType saved.bt) condition yes yesExit noEntry yesNormal ∧
      instruction = .IFELSE (Wasm2.blockType saved.bt) yes scope.source) := by
  obtain ⟨matched, params, results, source⟩ := same
  generalize hf : saved.form = form at closed matched params identity
  generalize ht : saved.bt = bt at closed matched
  generalize hs : saved.ops = body at closed source
  generalize sf : scope.form = current at matched
  cases closed <;> cases matched
  · exact .inl ⟨rfl, by rw [source]⟩
  · exact .inr (.inl ⟨rfl, by rw [source]⟩)
  · exact .inr (.inr (.inl ⟨_, rfl, by rw [source], by simpa [Wasm2.Frames.Form.params, identity rfl, results] using params⟩))
  · exact .inr (.inr (.inr ⟨_, _, _, _, _, rfl, by rw [source]⟩))
end Exec.Code
