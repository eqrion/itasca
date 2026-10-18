import Exec.Code.Body.Reader.Common.ReaderWasm1
import Itasca.Wasm1.StepControl
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm1 Itasca.VisitorTrace

structure ReaderEnterPostWasm1 {data env ctx bodyBt st}
    (p : Pending data env ctx bodyBt st) (out : code.OpIterState)
    (form : Frames.Form) (bt : code.BlockType) (remaining : List code.StackType)
    (token : Token) : Prop where
  encoded : At data p.start token out.pos
  popped : ∀ ts, Sequence.Realizes p.current.ctrl.polymorphic_base remaining ts →
    Sequence.Realizes p.current.ctrl.polymorphic_base p.current.vals (ts ++ form.inputs)
  opened : Frames.Open (EnvTranslation.context env ctx) out
    (p.parents ++ [{p.current with vals := remaining}]) (Frames.Saved.fresh out form bt)
  after : p.After out

theorem reader_block_wasm1 {data env ctx bodyBt st}
    (p : Pending data env ctx bodyBt st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_BLOCK)
    (accepted : code.step visitor st data env ctx code.OP_BLOCK before =
      .ok (.Ok (), out, after)) :
    ∃ bt, visitor.on_block before out (Control.signature bt) = .ok (.Ok (), after) ∧
      code.read_block st data = .ok (.Ok bt, out) ∧
      ReaderEnterPostWasm1 p out .block bt p.current.vals (.block bt) := by
  rw [dispatch_block] at accepted
  obtain ⟨bt, read, callback⟩ := reader_run_success _ _ _ _ _ accepted
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := p.opened
  have effect := code.read_block.raw_spec st data p.ctrl_capacity
  rw [read, WP.spec_ok] at effect
  obtain ⟨decoded, values, controls⟩ := effect bt rfl
  dsimp only at decoded values controls
  have popped : ∀ ts, Sequence.Realizes p.current.ctrl.polymorphic_base p.current.vals ts →
      Sequence.Realizes p.current.ctrl.polymorphic_base p.current.vals (ts ++ Frames.Form.block.inputs) := by
    intro ts ht
    simpa [Frames.Form.inputs] using ht
  obtain ⟨opened, trace⟩ := p.opened.enter_child (st' := out)
    (EnvTranslation.context_wf env ctx) .block bt (.inl rfl) p.current.vals popped
    (by simpa [Frames.Saved.fresh, Frames.Form.kind, Control.frame, values] using controls)
    (by simpa [vals, base] using congrArg alloc.vec.Vec.val values)
  have encoded : At data p.start (.block bt) out.pos :=
    .of_block_type bt p.inbounds (by simpa [global_simps] using byte) p.pos (.block bt) decoded
  refine ⟨bt, callback, read, encoded, popped, opened, ?_⟩
  apply p.running_after out _ _ (.block bt) encoded opened
  · simpa [Frames.bodyType_enter] using p.bodyType
  · simpa [Frames.Form.opening] using trace
  · simp [values]
  · simp [controls]

theorem reader_loop_wasm1 {data env ctx bodyBt st}
    (p : Pending data env ctx bodyBt st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_LOOP)
    (accepted : code.step visitor st data env ctx code.OP_LOOP before =
      .ok (.Ok (), out, after)) :
    ∃ bt, visitor.on_loop before out (Control.signature bt) = .ok (.Ok (), after) ∧
      code.read_loop st data = .ok (.Ok bt, out) ∧
      ReaderEnterPostWasm1 p out .loop bt p.current.vals (.loop bt) := by
  rw [dispatch_loop] at accepted
  obtain ⟨bt, read, callback⟩ := reader_run_success _ _ _ _ _ accepted
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := p.opened
  have effect := code.read_loop.raw_spec st data p.ctrl_capacity
  rw [read, WP.spec_ok] at effect
  obtain ⟨decoded, values, controls⟩ := effect bt rfl
  dsimp only at decoded values controls
  have popped : ∀ ts, Sequence.Realizes p.current.ctrl.polymorphic_base p.current.vals ts →
      Sequence.Realizes p.current.ctrl.polymorphic_base p.current.vals (ts ++ Frames.Form.loop.inputs) := by
    intro ts ht
    simpa [Frames.Form.inputs] using ht
  obtain ⟨opened, trace⟩ := p.opened.enter_child (st' := out)
    (EnvTranslation.context_wf env ctx) .loop bt (.inr (.inl rfl)) p.current.vals popped
    (by simpa [Frames.Saved.fresh, Frames.Form.kind, Control.frame, values] using controls)
    (by simpa [vals, base] using congrArg alloc.vec.Vec.val values)
  have encoded : At data p.start (.loop bt) out.pos :=
    .of_block_type bt p.inbounds (by simpa [global_simps] using byte) p.pos (.loop bt) decoded
  refine ⟨bt, callback, read, encoded, popped, opened, ?_⟩
  apply p.running_after out _ _ (.loop bt) encoded opened
  · simpa [Frames.bodyType_enter] using p.bodyType
  · simpa [Frames.Form.opening] using trace
  · simp [values]
  · simp [controls]

theorem reader_if_wasm1 {data env ctx bodyBt st}
    (p : Pending data env ctx bodyBt st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_IF)
    (accepted : code.step visitor st data env ctx code.OP_IF before =
      .ok (.Ok (), out, after)) :
    ∃ bt remaining, visitor.on_if before out (Control.signature bt) = .ok (.Ok (), after) ∧
      code.read_if st data = .ok (.Ok bt, out) ∧
      ReaderEnterPostWasm1 p out .then_ bt remaining (.if_ bt) := by
  rw [dispatch_if] at accepted
  obtain ⟨bt, read, callback⟩ := reader_run_success _ _ _ _ _ accepted
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := p.opened
  have effect := code.read_if.raw_spec st data outer p.current.vals vals
    (by simp [Control.base, ctrls, base]) p.ctrl_capacity
  rw [read, WP.spec_ok] at effect
  obtain ⟨decoded, remaining, values, length, controls, back⟩ := effect bt rfl
  dsimp only at decoded values length controls back
  have popped : ∀ ts, Sequence.Realizes p.current.ctrl.polymorphic_base remaining ts →
      Sequence.Realizes p.current.ctrl.polymorphic_base p.current.vals (ts ++ Frames.Form.then_.inputs) := by
    simpa [Frames.Form.inputs, Control.polymorphic, ctrls] using back
  obtain ⟨opened, trace⟩ := p.opened.enter_child (st' := out)
    (EnvTranslation.context_wf env ctx) .then_ bt (.inr (.inr rfl)) remaining popped
    (by simpa [Frames.Saved.fresh, Frames.Form.kind] using controls)
    (by simpa [vals, base] using values)
  have encoded : At data p.start (.if_ bt) out.pos :=
    .of_block_type bt p.inbounds (by simpa [global_simps] using byte) p.pos (.if_ bt) decoded
  refine ⟨bt, remaining, callback, read, encoded, popped, opened, ?_⟩
  apply p.running_after out _ _ (.if_ bt) encoded opened
  · simpa [Frames.bodyType_enter] using p.bodyType
  · simpa [Frames.Form.opening] using trace
  · simp only [values, vals, List.length_append]; omega
  · simp [controls]
end Exec.Code
