import Itasca.Support.Result
import Itasca.Visitor.VisitorControlDispatch
import Itasca.Visitor.VisitorSingleTrace
import Itasca.Visitor.BrTableTrace
import Itasca.Body.WasmStepControl
import Itasca.Body.WasmStepBranch

open Aeneas Aeneas.Std

namespace Itasca.VisitorTrace

theorem step_block {data env ctx bt st} (p : Wasm.Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_BLOCK) :
    StepRecords p visitor observe code.OP_BLOCK := by
  intro v result final v' h
  rw [dispatch_block] at h
  apply run_step_trace data p.start _ visitor observe hrecords (fun a => .block (Control.signature a)) ?_ v result final v' h
  intro s a hr
  have hs := code.read_block.raw_spec st data p.ctrl_capacity
  rw [hr, WP.spec_ok] at hs
  obtain ⟨hd, _, _⟩ := hs a rfl
  exact ⟨.block a, by cases a <;> rfl, by simp [Action.opcode],
    .of_block_type a p.inbounds (by simpa [global_simps] using hbyte) p.pos (.block a) hd⟩

theorem step_loop {data env ctx bt st} (p : Wasm.Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_LOOP) :
    StepRecords p visitor observe code.OP_LOOP := by
  intro v result final v' h
  rw [dispatch_loop] at h
  apply run_step_trace data p.start _ visitor observe hrecords (fun a => .loop (Control.signature a)) ?_ v result final v' h
  intro s a hr
  have hs := code.read_loop.raw_spec st data p.ctrl_capacity
  rw [hr, WP.spec_ok] at hs
  obtain ⟨hd, _, _⟩ := hs a rfl
  exact ⟨.loop a, by cases a <;> rfl, by simp [Action.opcode],
    .of_block_type a p.inbounds (by simpa [global_simps] using hbyte) p.pos (.loop a) hd⟩

theorem step_if {data env ctx bt st} (p : Wasm.Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_IF) :
    StepRecords p visitor observe code.OP_IF := by
  intro v result final v' h
  rw [dispatch_if] at h
  apply run_step_trace data p.start _ visitor observe hrecords (fun a => .if_ (Control.signature a)) ?_ v result final v' h
  intro s a hr
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := id p.opened
  have hs := code.read_if.raw_spec st data outer p.current.vals vals
    (by simp [Control.base, ctrls, base]) p.ctrl_capacity
  rw [hr, WP.spec_ok] at hs
  obtain ⟨hd, _⟩ := hs a rfl
  exact ⟨.if_ a, by cases a <;> rfl, by simp [Action.opcode],
    .of_block_type a p.inbounds (by simpa [global_simps] using hbyte) p.pos (.if_ a) hd⟩

theorem step_else {data env ctx bt st} (p : Wasm.Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_ELSE) :
    StepRecords p visitor observe code.OP_ELSE := by
  intro v result final v' h
  rw [dispatch_else] at h
  apply run_step_trace data p.start _ visitor observe hrecords (fun a => .else_ (Control.signature a)) ?_ v result final v' h
  intro s a hr
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := id p.opened
  have hs := code.read_else.realizes st (p.parents.map WasmFrames.Saved.ctrl)
    p.current.ctrl outer p.current.vals ctrls vals base
  rw [hr, WP.spec_ok] at hs
  have hp : s.pos = st.pos := hs.1
  exact ⟨.else_, rfl, by simp [Action.opcode],
    .no_immediate p.inbounds (by simpa [global_simps] using hbyte) (by simpa [hp] using p.pos) .else_⟩

theorem step_end {data env ctx bt st} (p : Wasm.Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_END) :
    StepRecords p visitor observe code.OP_END := by
  intro v result final v' h
  rw [dispatch_end] at h
  apply run_step_trace data p.start _ visitor observe hrecords (fun a : code.LabelKind × code.BlockType => .end_ a.1 (Control.signature a.2)) ?_ v result final v' h
  intro s a hr
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := id p.opened
  have hs := code.read_end.realizes st (p.parents.map WasmFrames.Saved.ctrl)
    p.current.ctrl outer p.current.vals ctrls vals base (Nat.le_of_lt p.val_capacity)
  rw [hr, WP.spec_ok] at hs
  have hp : s.pos = st.pos := hs.1
  exact ⟨.end_, rfl, by simp [Action.opcode],
    .no_immediate p.inbounds (by simpa [global_simps] using hbyte) (by simpa [hp] using p.pos) .end_⟩

theorem step_br {data env ctx bt st} (p : Wasm.Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_BR) :
    StepRecords p visitor observe code.OP_BR := by
  intro v result final v' h
  rw [dispatch_br] at h
  apply run_step_trace data p.start _ visitor observe hrecords (fun a : U32 × code.BlockType => .br a.1 (Control.resultView a.2)) ?_ v result final v' h
  rintro s ⟨depth, resultBt⟩ hr
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals, hC, labels, returns⟩ :=
    p.opened.context (EnvTranslation.context_wf env ctx)
  have hs := code.read_br.prefix st data (p.parents.map WasmFrames.Saved.ctrl)
    p.current.ctrl outer p.current.vals ctrls vals base _ hC p.current.ops typed
    (by simpa [EnvTranslation.context] using labels)
  rw [hr, WP.spec_ok] at hs
  obtain ⟨hd, _⟩ := hs depth resultBt rfl
  exact ⟨.plain (.BR (.mk_uN depth.val)), rfl, by simp [Action.opcode],
    .of_u32 depth p.inbounds (by simpa [global_simps] using hbyte) p.pos (fun _ => .br depth) hd⟩

theorem step_br_if {data env ctx bt st} (p : Wasm.Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_BR_IF) :
    StepRecords p visitor observe code.OP_BR_IF := by
  intro v result final v' h
  rw [dispatch_br_if] at h
  apply run_step_trace data p.start _ visitor observe hrecords (fun a : U32 × code.BlockType => .br_if a.1 (Control.resultView a.2)) ?_ v result final v' h
  rintro s ⟨depth, resultBt⟩ hr
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals, hC, labels, returns⟩ :=
    p.opened.context (EnvTranslation.context_wf env ctx)
  have hb : (Control.base st).val = outer.length := by simp [Control.base, ctrls, base]
  have hp : Control.polymorphic st = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic, ctrls]
  have hs := code.read_br_if.prefix st data outer p.current.vals vals hb
    (by have := p.val_capacity; omega) _ hC p.current.ops (by simpa [hp] using typed)
    (by simpa [EnvTranslation.context] using labels)
  rw [hr, WP.spec_ok] at hs
  obtain ⟨hd, _⟩ := hs depth resultBt rfl
  exact ⟨.plain (.BR_IF (.mk_uN depth.val)), rfl, by simp [Action.opcode],
    .of_u32 depth p.inbounds (by simpa [global_simps] using hbyte) p.pos (fun _ => .brIf depth) hd⟩

theorem step_return {data env ctx bt st} (p : Wasm.Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_RETURN) :
    StepRecords p visitor observe code.OP_RETURN := by
  intro v result final v' h
  rw [dispatch_return] at h
  apply run_step_trace data p.start _ visitor observe hrecords (fun _ => .return_) ?_ v result final v' h
  rintro s ⟨⟩ hr
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals, hC, labels, returns⟩ :=
    p.opened.context (EnvTranslation.context_wf env ctx)
  have hs := code.read_return.prefix st ctx (p.parents.map WasmFrames.Saved.ctrl)
    p.current.ctrl outer p.current.vals ctrls vals base _ hC p.current.ops typed
    (by simpa [EnvTranslation.context] using returns)
  rw [hr, WP.spec_ok] at hs
  obtain ⟨_, _, hp, _⟩ := hs rfl
  dsimp only at hp
  exact ⟨.plain .RETURN, rfl, by simp [Action.opcode],
    .no_immediate p.inbounds (by simpa [global_simps] using hbyte) (by simpa [hp] using p.pos) .return_⟩

/-- The table's final callback follows every vector callback and the unobserved
default, with all validation complete. A rejecting closing callback remains in
the complete byte chunk; any earlier failure leaves just its observed prefix. -/
theorem step_br_table {data env ctx bt st} (p : Wasm.Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_BR_TABLE) :
    StepRecords p visitor observe code.OP_BR_TABLE := by
  intro v result final v' h
  rw [code.step_br_table.dispatch] at h
  obtain ⟨⟨res, s, w⟩, hr, hrun⟩ := ResultFacts.bind_ok_inv _ _ _ h
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := id p.opened
  obtain ⟨observations, hlog, htrace⟩ := code.read_br_table.trace visitor observe hrecords
    st data v (p.parents.map WasmFrames.Saved.ctrl) p.current.ctrl outer p.current.vals
    ctrls vals base res s w hr
  have hopcode : Wasm.BytesAt data p.start [0x0E#u8] st.pos :=
    .byte data p.start st.pos 0x0E#u8 p.inbounds (by simpa [global_simps] using hbyte) p.pos
  rcases (CoreVisitor.run.returned_iff (.ok (res, s))
      (fun v s (a : U32 × code.BlockType) => visitor.on_br_table v s a.1 (Control.resultView a.2))
      w result final v').mp hrun with
    ⟨e, herr, rfl, rfl⟩ | ⟨a, reply, hok, hhook, rfl⟩
  · simp only [Result.ok.injEq, Prod.mk.injEq] at herr
    obtain ⟨rfl, rfl⟩ := herr
    obtain ⟨hpartial, hout⟩ := htrace
    refine ⟨observations, hlog, ?_⟩
    rcases hpartial with rfl | ⟨count, first, depths, last, hcount, hlabels, hlen⟩
    · exact .silent e s hout
    · exact .unfinished e ⟨st.pos, count, first, depths, last.pos, hopcode,
        hcount, hlabels.labelsAt, hlen⟩ hout
  · simp only [Result.ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨rfl, rfl⟩ := hok
    obtain ⟨fallback, common⟩ := a
    obtain ⟨count, first, depths, last, hcount, hlabels, hlen, hdefault, hall⟩ := htrace
    have hrecord := hrecords w (.op s (.br_table fallback (Control.resultView common))) reply v' hhook
    refine ⟨observations ++ [⟨.op s (.br_table fallback (Control.resultView common)), reply⟩], ?_, ?_⟩
    · simpa [hlog, List.append_assoc] using hrecord
    · refine .complete (.table hopcode hcount hlabels.labelsAt hlen hdefault ?_) ?_
      · exact .of_br_table count depths fallback p.inbounds
          (by simpa [global_simps] using hbyte) p.pos hcount hlen hlabels.decoded hdefault
      · exact (Outcomes.single (.op s (.br_table fallback (Control.resultView common))) reply).prepend hall

end Itasca.VisitorTrace
