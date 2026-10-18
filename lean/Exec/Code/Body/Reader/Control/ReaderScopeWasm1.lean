import Exec.Code.Body.Reader.Control.ReaderScope
import Exec.Code.Body.Reader.Common.ReaderCloseWasm1
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Only source syntax is matched here; control locations and liveness remain compiler ghosts. -/
inductive ScopeFormMatchesWasm1 (bt : code.BlockType) : ScopeForm → Wasm1.Frames.Form → Prop where
  | body : ScopeFormMatchesWasm1 bt .body .body
  | block : ScopeFormMatchesWasm1 bt (.block (Control.blockType bt)) .block
  | loop : ScopeFormMatchesWasm1 bt (.loop (Control.blockType bt)) .loop
  | then_ (condition) : ScopeFormMatchesWasm1 bt (.then_ (Control.blockType bt) condition) .then_
  | else_ (condition yesExit noEntry yesNormal tokens ops) :
      ScopeFormMatchesWasm1 bt (.else_ (Control.blockType bt) condition ops yesExit noEntry yesNormal) (.else_ tokens ops)

structure SourceScopeMatchesWasm1 (scope : SourceScope) (saved : Wasm1.Frames.Saved) : Prop where
  form : ScopeFormMatchesWasm1 saved.ctrl.block_type scope.form saved.form
  params : scope.params = []
  results : scope.results = Control.resultTypes saved.ctrl.block_type
  source : scope.source = saved.ops

theorem ScopeFormMatchesWasm1.kind {bt scope saved} (same : ScopeFormMatchesWasm1 bt scope saved) :
    scope.kind = saved.kind := by cases same <;> rfl

theorem SourceScopeMatchesWasm1.branchTypes {scope saved} (same : SourceScopeMatchesWasm1 scope saved) :
    scope.branchTypes = saved.form.label saved.ctrl.block_type := by
  obtain ⟨form, params, results, source⟩ := same
  generalize scopeForm : scope.form = f at form
  generalize savedForm : saved.form = g at form
  cases form <;> simp_all [SourceScope.branchTypes, Wasm1.Frames.Form.label]

theorem SourceScopeMatchesWasm1.advance_iff {scope saved}
    (token : Wasm1.Token) (instruction : instr) (poly : Bool) (values : List code.StackType) :
    SourceScopeMatchesWasm1 (scope.advance instruction) (saved.advance token instruction poly values) ↔
      SourceScopeMatchesWasm1 scope saved := by
  constructor
  · intro same
    exact ⟨same.form, same.params, same.results, List.append_cancel_right same.source⟩
  · intro same
    exact ⟨same.form, same.params, same.results, by simp [SourceScope.advance, Wasm1.Frames.Saved.advance, same.source]⟩

theorem SourceScopeMatchesWasm1.suspend {scope saved}
    (same : SourceScopeMatchesWasm1 scope saved) (values : List code.StackType) :
    SourceScopeMatchesWasm1 scope {saved with vals := values} := ⟨same.form, same.params, same.results, same.source⟩

theorem ScopeFormMatchesWasm1.then_inv {bt type condition saved}
    (same : ScopeFormMatchesWasm1 bt (.then_ type condition) saved) :
    type = Control.blockType bt ∧ saved = .then_ := by cases same; exact ⟨rfl, rfl⟩

theorem SourceScopeMatchesWasm1.begin_else {scope saved}
    (same : SourceScopeMatchesWasm1 scope saved) (type : blocktype) (condition : U32)
    (form : scope.form = .then_ type condition) (yesExit : Nat) (noEntry : U32) (yesNormal : Bool) :
    SourceScopeMatchesWasm1 (scope.begin_else type condition yesExit noEntry yesNormal) saved.nextElse := by
  obtain ⟨matched, params, results, source⟩ := same
  rw [form] at matched
  obtain ⟨rfl, savedForm⟩ := matched.then_inv
  refine ⟨?_, ?_, results, rfl⟩
  · simpa [SourceScope.begin_else, Wasm1.Frames.Saved.nextElse, source] using
      ScopeFormMatchesWasm1.else_ (bt := saved.ctrl.block_type) condition yesExit noEntry yesNormal saved.tokens saved.ops
  · simpa [SourceScope.begin_else, Wasm1.Frames.Saved.nextElse, savedForm] using params

theorem SourceScopeMatchesWasm1.resume {scope parent child instruction}
    (same : SourceScopeMatchesWasm1 scope parent) :
    SourceScopeMatchesWasm1 (scope.advance instruction) (resumedSourceWasm1 parent child instruction) :=
  ⟨same.form, same.params, same.results, by simp [SourceScope.advance, resumedSourceWasm1, same.source]⟩

/-- Actual ordinary readers append the same literal instruction to both source representations. -/
theorem ReaderPostWasm1.scope {data env ctx bt st out instruction poly values}
    {p : Wasm1.Pending data env ctx bt st} {scope}
    (post : ReaderPostWasm1 p out instruction poly values)
    (same : SourceScopeMatchesWasm1 scope p.current) :
    SourceScopeMatchesWasm1 (scope.advance instruction) (p.current.advance (.plain instruction) instruction poly values) ∧
      Wasm1.Frames.Open (EnvTranslation.context env ctx) out p.parents
        (p.current.advance (.plain instruction) instruction poly values) :=
  ⟨(SourceScopeMatchesWasm1.advance_iff _ _ _ _).mpr same, post.opened⟩

theorem ScopeFormMatchesWasm1.closed {bt scope saved source instruction}
    (same : ScopeFormMatchesWasm1 bt scope saved)
    (closed : Wasm1.Frames.Closed saved bt source instruction) :
    ScopeClosed scope source instruction := by
  cases closed <;> cases same <;> constructor

theorem SourceScopeMatchesWasm1.closed {scope saved instruction}
    (same : SourceScopeMatchesWasm1 scope saved)
    (closed : Wasm1.Frames.Closed saved.form saved.ctrl.block_type saved.ops instruction) :
    ScopeClosed scope.form scope.source instruction := by
  rw [same.source]
  exact same.form.closed closed

theorem SourceScopeMatchesWasm1.fresh (bt : code.BlockType) (form : Wasm1.Frames.Form)
    (scopeForm : ScopeForm) (matched : ScopeFormMatchesWasm1 bt scopeForm form)
    (state : code.OpIterState) (front : List valtype) (entry bodyPc : Nat) (entered : Bool) :
    SourceScopeMatchesWasm1
      ⟨scopeForm, front, [], Control.resultTypes bt, [], entry, bodyPc, entered⟩
      (Wasm1.Frames.Saved.fresh state form bt) :=
  ⟨matched, rfl, rfl, rfl⟩

end Exec.Code
