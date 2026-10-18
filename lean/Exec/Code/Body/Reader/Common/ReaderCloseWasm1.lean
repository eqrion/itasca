import Exec.Code.Body.Reader.Common.ReaderEnterWasm1
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm1 Itasca.VisitorTrace

def resumedSourceWasm1 (parent child : Frames.Saved) (instruction : instr) : Frames.Saved :=
  { parent with
    ops := parent.ops ++ [instruction]
    vals := parent.vals ++ (Control.results child.ctrl.block_type).map code.StackType.Val
    tokens := parent.tokens ++ child.trace ++ [.end_] }

def ReaderEndZipperWasm1 {data env ctx bodyBt st}
    (p : Pending data env ctx bodyBt st) (out : code.OpIterState) : Prop :=
  (p.current.form = .body ∧ p.parents = [] ∧
    BodyTokens (Frames.trace p.parents p.current ++ [.end_]) p.current.ops ∧
    Instrs_ok (Frames.enter (EnvTranslation.context env ctx) .body p.current.ctrl.block_type)
      p.current.ops (.mk_functype (.mk_list []) (.mk_list (Control.resultTypes p.current.ctrl.block_type))) ∧
    Instructions (Frames.enter (EnvTranslation.context env ctx) .body p.current.ctrl.block_type) p.current.ops) ∨
  ∃ grandparents parent instruction, p.parents = grandparents ++ [parent] ∧
    Frames.Closed p.current.form p.current.ctrl.block_type p.current.ops instruction ∧
    Frames.Open (EnvTranslation.context env ctx) out grandparents
      (resumedSourceWasm1 parent p.current instruction)

theorem reader_end_wasm1 {data env ctx bodyBt st}
    (p : Pending data env ctx bodyBt st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_END)
    (accepted : code.step visitor st data env ctx code.OP_END before = .ok (.Ok (), out, after)) :
    visitor.on_end before out p.current.ctrl.kind (Control.signature p.current.ctrl.block_type) = .ok (.Ok (), after) ∧
    code.read_end st = .ok (.Ok (p.current.ctrl.kind, p.current.ctrl.block_type), out) ∧
    At data p.start .end_ out.pos ∧
    Sequence.Realizes p.current.ctrl.polymorphic_base p.current.vals (Control.resultTypes p.current.ctrl.block_type) ∧
    ReaderEndZipperWasm1 p out ∧ p.After out := by
  rw [dispatch_end] at accepted
  obtain ⟨⟨kind, bt⟩, read, callback⟩ := reader_run_success _ _ _ _ _ accepted
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := p.opened
  have effect := code.read_end.realizes st (p.parents.map Frames.Saved.ctrl) p.current.ctrl
    outer p.current.vals ctrls vals base (Nat.le_of_lt p.val_capacity)
  rw [read, WP.spec_ok] at effect
  obtain ⟨position, rfl, rfl, controls, values, results, thenEmpty⟩ := effect
  dsimp only at position controls values results thenEmpty
  have encoded : At data p.start .end_ out.pos :=
    .no_immediate p.inbounds (by simpa [global_simps] using byte) (by simpa [position] using p.pos) .end_
  have generic := code.read_end.wasm1_frames (EnvTranslation.context env ctx)
    (EnvTranslation.context_wf env ctx) st p.parents p.current bodyBt p.opened p.bodyType
    (Nat.le_of_lt p.val_capacity)
  rw [read, WP.spec_ok] at generic
  obtain ⟨_, post⟩ := generic
  obtain ⟨valBound, ctrlBound, status⟩ := post _ rfl
  dsimp only at valBound ctrlBound status
  have afterState : p.After out := by
    rcases status with ⟨parents, current, opened, trace, body⟩ | ⟨controls, ops, body, typed, profile⟩
    · exact p.running_after out parents current .end_ encoded opened body trace valBound (by omega)
    · exact p.closed_after out ops encoded controls body typed profile valBound
  refine ⟨callback, read, encoded, results, ?_, afterState⟩
  by_cases root : p.current.form = .body
  · exact .inl ⟨root, p.opened.finish_body root results⟩
  · have closed : ∃ op, Frames.Closed p.current.form p.current.ctrl.block_type p.current.ops op := by
      cases form : p.current.form with
      | body => exact False.elim (root form)
      | block => exact ⟨_, .block _ _⟩
      | loop => exact ⟨_, .loop _ _⟩
      | then_ =>
        have empty := thenEmpty (by rw [header.kind, form]; rfl)
        rw [empty]
        exact ⟨_, .then_ _⟩
      | else_ tokens ops => exact ⟨_, .else_ _ _ _ _⟩
    obtain ⟨instruction, closed⟩ := closed
    obtain ⟨grandparents, parent, parents, opened, trace⟩ := p.opened.close
      (EnvTranslation.context_wf env ctx) instruction closed results controls
      (by simpa [vals, base] using values)
    exact .inr ⟨grandparents, parent, instruction, parents, closed, opened⟩

theorem reader_else_wasm1 {data env ctx bodyBt st}
    (p : Pending data env ctx bodyBt st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_ELSE)
    (accepted : code.step visitor st data env ctx code.OP_ELSE before = .ok (.Ok (), out, after)) :
    visitor.on_else before out (Control.signature p.current.ctrl.block_type) = .ok (.Ok (), after) ∧
    code.read_else st = .ok (.Ok p.current.ctrl.block_type, out) ∧
    p.current.form = .then_ ∧ At data p.start .else_ out.pos ∧
    Sequence.Realizes p.current.ctrl.polymorphic_base p.current.vals (Control.resultTypes p.current.ctrl.block_type) ∧
    Frames.Open (EnvTranslation.context env ctx) out p.parents p.current.nextElse ∧ p.After out := by
  rw [dispatch_else] at accepted
  obtain ⟨bt, read, callback⟩ := reader_run_success _ _ _ _ _ accepted
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := p.opened
  have effect := code.read_else.realizes st (p.parents.map Frames.Saved.ctrl) p.current.ctrl
    outer p.current.vals ctrls vals base
  rw [read, WP.spec_ok] at effect
  obtain ⟨position, kind, rfl, controls, values, results⟩ := effect
  dsimp only at position kind controls values results
  have form : p.current.form = .then_ := by
    rw [header.kind] at kind
    cases hf : p.current.form <;> simp_all [Frames.Form.kind]
  have encoded : At data p.start .else_ out.pos :=
    .no_immediate p.inbounds (by simpa [global_simps] using byte) (by simpa [position] using p.pos) .else_
  obtain ⟨opened, trace⟩ := p.opened.else_ (EnvTranslation.context_wf env ctx) form results controls
    (by simpa [vals, base] using values)
  refine ⟨callback, read, form, encoded, results, opened, ?_⟩
  refine p.running_after out p.parents p.current.nextElse .else_ encoded opened ?_ trace ?_ ?_
  · simpa [Frames.bodyType_else] using p.bodyType
  · simp only [values, vals, List.length_append]; omega
  · simp [controls, ctrls]
end Exec.Code
