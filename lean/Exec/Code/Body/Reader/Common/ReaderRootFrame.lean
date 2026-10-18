import Exec.Code.Body.Reader.Control.ReaderScopeZipper
import Exec.Code.Local.Callbacks.Control.ScopeFrameStack
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

private theorem paired_head_right {α β : Type} {R : α → β → Prop} {left right}
    (paired : List.Forall₂ R left right) (value : β) (found : right.head? = some value) :
    ∃ item, left.head? = some item ∧ R item value := by
  cases paired with
  | nil => simp at found
  | cons head tail =>
    simp only [List.head?_cons, Option.some.injEq] at found
    subst value
    exact ⟨_, rfl, head⟩

private theorem head_member {α : Type} {items : List α} {item}
    (found : items.head? = some item) : item ∈ items := by
  cases items with
  | nil => simp at found
  | cons first rest => simp only [List.head?_cons, Option.some.injEq] at found; subst item; simp

theorem reader_root_frame_wasm2 {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (compiler : runtime.compiler.FunctionCompiler A) {locals parents current}
    (physical : ScopeFrameStack locals compiler parents current)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current) :
    ∃ frame, compiler.frames.val[0]? = some frame ∧
      frame.results.val = slots (p.ft.results.val.map Translate.valueType) := by
  have bodyType := p.bodyType
  unfold Wasm2.Frames.bodyType at bodyType
  obtain ⟨saved, savedHead, savedType⟩ := Option.map_eq_some_iff.mp bodyType
  have sources := List.rel_append same.parents (.cons same.current .nil)
  obtain ⟨scope, scopeHead, matched⟩ := paired_head_right sources saved savedHead
  obtain ⟨frame, frameHead, framed⟩ := paired_head_right (List.Forall₂.flip physical.frames) scope scopeHead
  obtain ⟨C, outer, spine, header, _⟩ := p.opened
  have savedHeader : ∃ C, Wasm2.Frames.Header env C saved := by
    have member := head_member savedHead
    rcases List.mem_append.mp member with member | member
    · exact spine.headers saved member
    · have eq : saved = p.current := by simpa using member
      subst saved
      exact ⟨C, header⟩
  obtain ⟨D, savedHeader⟩ := savedHeader
  have outs := savedHeader.outputs
  rw [savedType] at outs
  have outputs : saved.outs = p.ft.results.val := by
    simpa [Wasm2.outputs, Wasm2.resolve, p.signature] using outs.symm
  refine ⟨frame, ?_, ?_⟩
  · simpa only [List.head?_eq_getElem?] using frameHead
  · rw [framed.results, matched.results, outputs]

theorem reader_root_frame_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (compiler : runtime.compiler.FunctionCompiler A) {locals parents current}
    (physical : ScopeFrameStack locals compiler parents current)
    (same : ReaderScopeZipperWasm1 parents current p.parents p.current) :
    ∃ frame, compiler.frames.val[0]? = some frame ∧ frame.results.val = slots (Control.resultTypes bt) := by
  have bodyType := p.bodyType
  unfold Wasm1.Frames.bodyType at bodyType
  obtain ⟨saved, savedHead, savedType⟩ := Option.map_eq_some_iff.mp bodyType
  have sources := List.rel_append same.parents (.cons same.current .nil)
  obtain ⟨scope, scopeHead, matched⟩ := paired_head_right sources saved savedHead
  obtain ⟨frame, frameHead, framed⟩ := paired_head_right (List.Forall₂.flip physical.frames) scope scopeHead
  refine ⟨frame, ?_, ?_⟩
  · simpa only [List.head?_eq_getElem?] using frameHead
  · rw [framed.results, matched.results, savedType]
end Exec.Code
