import Exec.Code.Local.Callbacks.Control.ElseSource
import Exec.Code.Body.Reader.Common.ReaderCloseWasm2
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Only source syntax is matched here; control locations and liveness remain compiler ghosts. -/
inductive ScopeFormMatchesWasm2 (bt : signature.BlockType) : ScopeForm → Wasm2.Frames.Form → Prop where
  | body : ScopeFormMatchesWasm2 bt .body .body
  | block : ScopeFormMatchesWasm2 bt (.block (Wasm2.blockType bt)) .block
  | loop : ScopeFormMatchesWasm2 bt (.loop (Wasm2.blockType bt)) .loop
  | then_ (condition) : ScopeFormMatchesWasm2 bt (.then_ (Wasm2.blockType bt) condition) .then_
  | else_ (condition yesExit noEntry yesNormal tokens ops) :
      ScopeFormMatchesWasm2 bt (.else_ (Wasm2.blockType bt) condition ops yesExit noEntry yesNormal) (.else_ tokens ops)

structure SourceScopeMatchesWasm2 (scope : SourceScope) (saved : Wasm2.Frames.Saved) : Prop where
  form : ScopeFormMatchesWasm2 saved.bt scope.form saved.form
  params : scope.params = (saved.form.params saved.ins).map Translate.valueType
  results : scope.results = saved.outs.map Translate.valueType
  source : scope.source = saved.ops

theorem ScopeFormMatchesWasm2.kind {bt scope saved} (same : ScopeFormMatchesWasm2 bt scope saved) :
    scope.kind = saved.kind := by cases same <;> rfl

theorem SourceScopeMatchesWasm2.branchTypes {scope saved} (same : SourceScopeMatchesWasm2 scope saved) :
    scope.branchTypes = saved.form.label saved.ins saved.outs := by
  obtain ⟨form, params, results, source⟩ := same
  generalize scopeForm : scope.form = f at form
  generalize savedForm : saved.form = g at form
  cases form <;> simp_all [SourceScope.branchTypes, Wasm2.Frames.Form.label, Wasm2.Frames.Form.params]

theorem SourceScopeMatchesWasm2.advance_iff {scope saved}
    (token : Wasm2.Token) (instruction : instr) (poly : Bool) (values : List code.StackType) :
    SourceScopeMatchesWasm2 (scope.advance instruction) (saved.advance token instruction poly values) ↔
      SourceScopeMatchesWasm2 scope saved := by
  constructor
  · intro same
    exact ⟨same.form, same.params, same.results, List.append_cancel_right same.source⟩
  · intro same
    exact ⟨same.form, same.params, same.results, by simp [SourceScope.advance, Wasm2.Frames.Saved.advance, same.source]⟩

theorem SourceScopeMatchesWasm2.suspend {scope saved}
    (same : SourceScopeMatchesWasm2 scope saved) (values : List code.StackType) :
    SourceScopeMatchesWasm2 scope {saved with vals := values} := ⟨same.form, same.params, same.results, same.source⟩

theorem ScopeFormMatchesWasm2.then_inv {bt type condition saved}
    (same : ScopeFormMatchesWasm2 bt (.then_ type condition) saved) :
    type = Wasm2.blockType bt ∧ saved = .then_ := by cases same; exact ⟨rfl, rfl⟩

theorem SourceScopeMatchesWasm2.begin_else {scope saved}
    (same : SourceScopeMatchesWasm2 scope saved) (type : blocktype) (condition : U32)
    (form : scope.form = .then_ type condition) (yesExit : Nat) (noEntry : U32) (yesNormal : Bool) :
    SourceScopeMatchesWasm2 (scope.begin_else type condition yesExit noEntry yesNormal) saved.nextElse := by
  obtain ⟨matched, params, results, source⟩ := same
  rw [form] at matched
  obtain ⟨rfl, savedForm⟩ := matched.then_inv
  refine ⟨?_, ?_, results, rfl⟩
  · simpa [SourceScope.begin_else, Wasm2.Frames.Saved.nextElse, source] using
      ScopeFormMatchesWasm2.else_ (bt := saved.bt) condition yesExit noEntry yesNormal saved.tokens saved.ops
  · simpa [SourceScope.begin_else, Wasm2.Frames.Saved.nextElse, savedForm, Wasm2.Frames.Form.params] using params

theorem SourceScopeMatchesWasm2.resume {scope parent child instruction}
    (same : SourceScopeMatchesWasm2 scope parent) :
    SourceScopeMatchesWasm2 (scope.advance instruction) (resumedSource parent child instruction) :=
  ⟨same.form, same.params, same.results, by simp [SourceScope.advance, resumedSource, same.source]⟩

theorem SourceScopeMatchesWasm2.fresh (bt : signature.BlockType) (form : Wasm2.Frames.Form)
    (scopeForm : ScopeForm) (matched : ScopeFormMatchesWasm2 bt scopeForm form)
    (base : Usize) (ins outs : List types.ValueType) (front : List valtype) (entry bodyPc : Nat) (entered : Bool) :
    SourceScopeMatchesWasm2
      ⟨scopeForm, front, (form.params ins).map Translate.valueType, outs.map Translate.valueType, [], entry, bodyPc, entered⟩
      (Wasm2.Frames.Saved.fresh base form bt ins outs) :=
  ⟨matched, rfl, rfl, rfl⟩

end Itasca.Runtime.Code
