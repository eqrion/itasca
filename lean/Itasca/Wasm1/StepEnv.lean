import Itasca.Wasm1.Profile
import Itasca.Wasm1.Invariant
import Itasca.Handler.EnvDispatch

/-!
# Wasm 1.0 environment-dependent steps

For each instruction whose typing consults the environment (`local.get`, `local.set`,
`local.tee`, `global.get`, `global.set`, `call`, `call_indirect`, `memory.size`, `memory.grow`
and the loads and stores), shows that `code.step` either rejects or reaches `Pending.After`.
The environment-dependent typing premises come from `EnvTranslation.Matches`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm1

private theorem run_after {A V : Type} {data env ctx bt st}
    (p : Pending data env ctx bt st)
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (hook : V → code.OpIterState → A → Result (core.result.Result Unit error.VisitError × V))
    (v : V) (hread : read ⦃ r => ∀ a, r.1 = .Ok a → p.After r.2 ⦄)
    (hhook : ∀ s a, ∃ res v', hook v s a = .ok (res, v')) :
    CoreVisitor.run read hook v ⦃ r => r.1 = .Ok () → p.After r.2.1 ⦄ := by
  refine WP.spec_mono (CoreVisitor.run.spec read hook v (fun _ => True) (fun _ s => p.After s)
    (WP.spec_mono hread (fun _ h => ⟨trivial, h⟩)) hhook) ?_
  intro r h hr
  obtain ⟨_, ha⟩ := h.2 hr
  exact ha

private theorem Pending.index_post_after {data env ctx bt st} (p : Pending data env ctx bt st)
    (C : context) (outer : List code.StackType)
    (spine : Wasm1.Frames.Spine (EnvTranslation.context env ctx) p.parents C outer p.current.form)
    (header : Wasm1.Frames.Header C p.current)
    (base : p.current.ctrl.value_stack_base.val = outer.length)
    (ctrls : st.ctrls.val = p.parents.map Wasm1.Frames.Saved.ctrl ++ [p.current.ctrl])
    (vals : st.vals.val = outer ++ p.current.vals)
    (opcode : U8) (op : U32 → instr) (hbyte : data.val[p.start.val]'p.inbounds = opcode)
    (hwf : ∀ idx, wf_instr (op idx))
    (himm : ∀ idx bytes, Leb128.Encoding bytes idx.val → Immediate opcode (.plain (op idx)) bytes)
    (r : core.result.Result U32 error.OpError × code.OpIterState)
    (hpost : EnvOps.IndexPost data st outer p.current.vals
      (Wasm1.Frames.enter C p.current.form p.current.ctrl.block_type) p.current.ops op r)
    (idx : U32) (hr : r.1 = .Ok idx)
    (hprofile : ∀ C idx, Wasm1.Instruction C (op idx) := by intro C idx; exact .leaf _ _ (by trivial)) : p.After r.2 := by
  obtain ⟨hd, hc, rest, hv, hl, ht⟩ := hpost idx hr
  have hpoly : Control.polymorphic st = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  apply p.append_result C outer spine header base ctrls vals r.2 (op idx)
    p.current.ctrl.polymorphic_base rest (hwf idx) _ (by simpa [hpoly] using ht) _ hv hl (hprofile _ idx)
  · obtain ⟨bytes, hs, hn, hb, he⟩ := hd
    exact .of_immediate p.inbounds hbyte p.pos (himm idx bytes he) ⟨hs, hn, hb⟩
  · simp [hc, ctrls]

/-- `code.step` on `code.OP_LOCAL_GET` either rejects or reaches `Pending.After`. -/
theorem Pending.step_local_get {data env ctx bt st} (p : Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hvisitor : FullVisitor.Total visitor)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x20#u8) :
    code.step visitor st data env ctx code.OP_LOCAL_GET v ⦃ r => r.1 = .Ok () → p.After r.2.1 ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := id p.opened
  have hpoly : Control.polymorphic st = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ctx (Wasm1.Frames.enter C p.current.form p.current.ctrl.block_type) :=
    spine.matches.enter _
  rw [code.step_local_get.dispatch]
  apply run_after p _ _ v _ (hvisitor.on_local_get v)
  refine WP.spec_mono (code.read_local_get.prefix st data env ctx outer p.current.vals vals
    (by have := p.val_capacity; omega) _ hC p.current.ops (by simpa [hpoly] using typed)) ?_
  intro r hr idx hi
  exact p.index_post_after C outer spine header base ctrls vals 0x20#u8 _ hbyte
    (fun idx => .instr_case_43 _ (EnvTranslation.index_wf idx))
    (fun idx _ he => .localGet idx he) r hr idx hi

/-- `code.step` on `code.OP_LOCAL_SET` either rejects or reaches `Pending.After`. -/
theorem Pending.step_local_set {data env ctx bt st} (p : Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hvisitor : FullVisitor.Total visitor)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x21#u8) :
    code.step visitor st data env ctx code.OP_LOCAL_SET v ⦃ r => r.1 = .Ok () → p.After r.2.1 ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := id p.opened
  have hpoly : Control.polymorphic st = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ctx (Wasm1.Frames.enter C p.current.form p.current.ctrl.block_type) :=
    spine.matches.enter _
  rw [code.step_local_set.dispatch]
  apply run_after p _ _ v _ (hvisitor.on_local_set v)
  refine WP.spec_mono (code.read_local_set.prefix st data env ctx outer p.current.vals vals
    (by simpa [Control.base, ctrls] using base) _ hC p.current.ops (by simpa [hpoly] using typed)) ?_
  intro r hr idx hi
  exact p.index_post_after C outer spine header base ctrls vals 0x21#u8 _ hbyte
    (fun idx => .instr_case_44 _ (EnvTranslation.index_wf idx))
    (fun idx _ he => .localSet idx he) r hr idx hi

/-- `code.step` on `code.OP_LOCAL_TEE` either rejects or reaches `Pending.After`. -/
theorem Pending.step_local_tee {data env ctx bt st} (p : Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hvisitor : FullVisitor.Total visitor)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x22#u8) :
    code.step visitor st data env ctx code.OP_LOCAL_TEE v ⦃ r => r.1 = .Ok () → p.After r.2.1 ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := id p.opened
  have hpoly : Control.polymorphic st = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ctx (Wasm1.Frames.enter C p.current.form p.current.ctrl.block_type) :=
    spine.matches.enter _
  rw [code.step_local_tee.dispatch]
  apply run_after p _ _ v _ (hvisitor.on_local_tee v)
  refine WP.spec_mono (code.read_local_tee.prefix st data env ctx outer p.current.vals vals
    (by simpa [Control.base, ctrls] using base)
    (by have := p.val_capacity; omega) _ hC p.current.ops (by simpa [hpoly] using typed)) ?_
  intro r hr idx hi
  exact p.index_post_after C outer spine header base ctrls vals 0x22#u8 _ hbyte
    (fun idx => .instr_case_45 _ (EnvTranslation.index_wf idx))
    (fun idx _ he => .localTee idx he) r hr idx hi

/-- `code.step` on `code.OP_GLOBAL_GET` either rejects or reaches `Pending.After`. -/
theorem Pending.step_global_get {data env ctx bt st} (p : Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hvisitor : FullVisitor.Total visitor)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x23#u8) :
    code.step visitor st data env ctx code.OP_GLOBAL_GET v ⦃ r => r.1 = .Ok () → p.After r.2.1 ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := id p.opened
  have hpoly : Control.polymorphic st = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ctx (Wasm1.Frames.enter C p.current.form p.current.ctrl.block_type) :=
    spine.matches.enter _
  rw [code.step_global_get.dispatch]
  apply run_after p _ _ v _ (hvisitor.on_global_get v)
  refine WP.spec_mono (code.read_global_get.prefix st data env ctx outer p.current.vals vals
    (by have := p.val_capacity; omega) _ hC p.current.ops (by simpa [hpoly] using typed)) ?_
  intro r hr idx hi
  exact p.index_post_after C outer spine header base ctrls vals 0x23#u8 _ hbyte
    (fun idx => .instr_case_46 _ (EnvTranslation.index_wf idx))
    (fun idx _ he => .globalGet idx he) r hr idx hi

/-- `code.step` on `code.OP_GLOBAL_SET` either rejects or reaches `Pending.After`. -/
theorem Pending.step_global_set {data env ctx bt st} (p : Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hvisitor : FullVisitor.Total visitor)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x24#u8) :
    code.step visitor st data env ctx code.OP_GLOBAL_SET v ⦃ r => r.1 = .Ok () → p.After r.2.1 ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := id p.opened
  have hpoly : Control.polymorphic st = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ctx (Wasm1.Frames.enter C p.current.form p.current.ctrl.block_type) :=
    spine.matches.enter _
  rw [code.step_global_set.dispatch]
  apply run_after p _ _ v _ (hvisitor.on_global_set v)
  refine WP.spec_mono (code.read_global_set.prefix st data env ctx outer p.current.vals vals
    (by simpa [Control.base, ctrls] using base) _ hC p.current.ops (by simpa [hpoly] using typed)) ?_
  intro r hr idx hi
  exact p.index_post_after C outer spine header base ctrls vals 0x24#u8 _ hbyte
    (fun idx => .instr_case_47 _ (EnvTranslation.index_wf idx))
    (fun idx _ he => .globalSet idx he) r hr idx hi

/-- `code.step` on `code.OP_CALL` either rejects or reaches `Pending.After`. -/
theorem Pending.step_call {data env ctx bt st} (p : Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hvisitor : FullVisitor.Total visitor)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x10#u8) :
    code.step visitor st data env ctx code.OP_CALL v ⦃ r => r.1 = .Ok () → p.After r.2.1 ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := id p.opened
  have hpoly : Control.polymorphic st = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ctx (Wasm1.Frames.enter C p.current.form p.current.ctrl.block_type) :=
    spine.matches.enter _
  rw [code.step_call.dispatch]
  apply run_after p _ _ v _ (hvisitor.on_call v)
  refine WP.spec_mono (code.read_call.prefix st data env ctx outer p.current.vals vals
    (by simpa [Control.base, ctrls] using base)
    (by have := p.val_capacity; omega) _ hC p.current.ops (by simpa [hpoly] using typed)) ?_
  intro r hr idx hi
  exact p.index_post_after C outer spine header base ctrls vals 0x10#u8 _ hbyte
    (fun idx => .instr_case_10 _ (EnvTranslation.index_wf idx))
    (fun idx _ he => .call idx he) r hr idx hi

/-- `code.step` on `code.OP_CALL_INDIRECT` either rejects or reaches `Pending.After`. -/
theorem Pending.step_call_indirect {data env ctx bt st} (p : Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hvisitor : FullVisitor.Total visitor)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x11#u8) :
    code.step visitor st data env ctx code.OP_CALL_INDIRECT v ⦃ r => r.1 = .Ok () → p.After r.2.1 ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := id p.opened
  have hpoly : Control.polymorphic st = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ctx (Wasm1.Frames.enter C p.current.form p.current.ctrl.block_type) :=
    spine.matches.enter _
  rw [code.step_call_indirect.dispatch]
  apply run_after p _ _ v _ (fun s idx => hvisitor.on_call_indirect v s idx 0#u32)
  refine WP.spec_mono (code.read_call_indirect.prefix st data env ctx outer p.current.vals vals
    (by simpa [Control.base, ctrls] using base) (by have := p.val_capacity; omega)
    _ hC p.current.ops (by simpa [hpoly] using typed)) ?_
  intro r hr idx hi
  obtain ⟨⟨middle, hd, hm, hz, hn⟩, hc, rest, hv, hl, ht⟩ := hr idx hi
  apply p.append_result C outer spine header base ctrls vals r.2
    (.CALL_INDIRECT (.mk_uN 0) (.mk_uN idx.val)) p.current.ctrl.polymorphic_base rest
    (.instr_case_11 _ _ (EnvTranslation.index_wf 0#u32) (EnvTranslation.index_wf idx)) _
    (by simpa [hpoly] using ht) _ hv hl
  · obtain ⟨bytes, hs, hn', hb, he⟩ := hd
    exact .of_immediate p.inbounds hbyte p.pos (.callIndirect idx he)
      ((show BytesAt data st.pos bytes middle from ⟨hs, hn', hb⟩).append
        (.byte data middle r.2.pos 0#u8 hm hz hn))
  · simp [hc, ctrls]

private theorem Pending.reserved_post_after {data env ctx bt st} (p : Pending data env ctx bt st)
    (C : context) (outer : List code.StackType)
    (spine : Wasm1.Frames.Spine (EnvTranslation.context env ctx) p.parents C outer p.current.form)
    (header : Wasm1.Frames.Header C p.current)
    (base : p.current.ctrl.value_stack_base.val = outer.length)
    (ctrls : st.ctrls.val = p.parents.map Wasm1.Frames.Saved.ctrl ++ [p.current.ctrl])
    (vals : st.vals.val = outer ++ p.current.vals)
    (opcode : U8) (op : instr) (hbyte : data.val[p.start.val]'p.inbounds = opcode)
    (hwf : wf_instr op) (himm : Immediate opcode (.plain op) [0#u8])
    (r : core.result.Result Unit error.OpError × code.OpIterState)
    (hpost : EnvOps.ReservedPost data st outer p.current.vals
      (Wasm1.Frames.enter C p.current.form p.current.ctrl.block_type) p.current.ops op r)
    (hr : r.1 = .Ok ())
    (hprofile : ∀ C, Wasm1.Instruction C op := by intro C; exact .leaf _ _ (by trivial)) : p.After r.2 := by
  obtain ⟨⟨hp, hz, hn⟩, hc, rest, hv, hl, ht⟩ := hpost hr
  have hpoly : Control.polymorphic st = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  apply p.append_result C outer spine header base ctrls vals r.2 op
    p.current.ctrl.polymorphic_base rest hwf _ (by simpa [hpoly] using ht) _ hv hl
    (hprofile _)
  · exact .of_immediate p.inbounds hbyte p.pos himm (.byte data st.pos r.2.pos 0#u8 hp hz hn)
  · simp [hc, ctrls]

/-- `code.step` on `code.OP_MEMORY_SIZE` either rejects or reaches `Pending.After`. -/
theorem Pending.step_memory_size {data env ctx bt st} (p : Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hvisitor : FullVisitor.Total visitor)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x3F#u8) :
    code.step visitor st data env ctx code.OP_MEMORY_SIZE v ⦃ r => r.1 = .Ok () → p.After r.2.1 ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := id p.opened
  have hpoly : Control.polymorphic st = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ctx (Wasm1.Frames.enter C p.current.form p.current.ctrl.block_type) :=
    spine.matches.enter _
  rw [code.step_memory_size.dispatch]
  apply run_after p _ _ v _ (fun s _ => hvisitor.on_memory_size v s)
  refine WP.spec_mono (code.read_memory_size.prefix st data env ctx outer p.current.vals vals
    (by have := p.val_capacity; omega) _ hC p.current.ops (by simpa [hpoly] using typed)) ?_
  intro r hr u hi
  cases u
  exact p.reserved_post_after C outer spine header base ctrls vals 0x3F#u8 _ hbyte
    .instr_case_62 .memorySize r hr hi

/-- `code.step` on `code.OP_MEMORY_GROW` either rejects or reaches `Pending.After`. -/
theorem Pending.step_memory_grow {data env ctx bt st} (p : Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hvisitor : FullVisitor.Total visitor)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x40#u8) :
    code.step visitor st data env ctx code.OP_MEMORY_GROW v ⦃ r => r.1 = .Ok () → p.After r.2.1 ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := id p.opened
  have hpoly : Control.polymorphic st = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ctx (Wasm1.Frames.enter C p.current.form p.current.ctrl.block_type) :=
    spine.matches.enter _
  rw [code.step_memory_grow.dispatch]
  apply run_after p _ _ v _ (fun s _ => hvisitor.on_memory_grow v s)
  refine WP.spec_mono (code.read_memory_grow.prefix st data env ctx outer p.current.vals vals
    (by simpa [Control.base, ctrls] using base) (by have := p.val_capacity; omega)
    _ hC p.current.ops (by simpa [hpoly] using typed)) ?_
  intro r hr u hi
  cases u
  exact p.reserved_post_after C outer spine header base ctrls vals 0x40#u8 _ hbyte
    .instr_case_63 .memoryGrow r hr hi

/-- `code.step` on a load or store opcode with meaning `operation` either rejects or reaches
`Pending.After`. -/
theorem Pending.step_memory {data env ctx bt st} (p : Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hvisitor : FullVisitor.Total visitor)
    (opcode : U8) (operation : MemoryMeaning.Operation)
    (hbyte : data.val[p.start.val]'p.inbounds = opcode)
    (hrow : MemoryMeaning.opcodeMeaning opcode = some operation) :
    code.step visitor st data env ctx opcode v ⦃ r => r.1 = .Ok () → p.After r.2.1 ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := id p.opened
  have hpoly : Control.polymorphic st = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ctx (Wasm1.Frames.enter C p.current.form p.current.ctrl.block_type) :=
    spine.matches.enter _
  have hb : (Control.base st).val = outer.length := by simpa [Control.base, ctrls] using base
  have hread : (if operation.store then code.read_store st data env operation.ty operation.naturalAlign
      else code.read_load st data env operation.ty operation.naturalAlign) ⦃
        EnvOps.MemoryPost data st outer p.current.vals
          (Wasm1.Frames.enter C p.current.form p.current.ctrl.block_type) p.current.ops operation.op ⦄ := by
    cases hs : operation.store with
    | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact code.read_load.prefix st data env ctx outer p.current.vals vals hb
          (by have := p.val_capacity; omega) _ hC p.current.ops (by simpa [hpoly] using typed)
          opcode operation hrow hs
    | true =>
        simp only [↓reduceIte]
        exact code.read_store.prefix st data env ctx outer p.current.vals vals hb
          _ hC p.current.ops (by simpa [hpoly] using typed) opcode operation hrow hs
  rw [code.step_memory.dispatch visitor st data env ctx v opcode operation hrow]
  apply run_after p _ _ v _ (fun s arg => hvisitor.visit_memory v s opcode arg)
  refine WP.spec_mono hread ?_
  intro r hr arg hi
  obtain ⟨⟨middle, halign, hoffset⟩, hc, rest, hv, hl, ht⟩ := hr arg hi
  have hwf : wf_instr (operation.op arg) := ht.wellFormed _ (by simp)
  apply p.append_result C outer spine header base ctrls vals r.2 (operation.op arg)
    p.current.ctrl.polymorphic_base rest hwf _ (by simpa [hpoly] using ht) _ hv hl
    (MemoryMeaning.opcode_profile opcode operation hrow _ arg)
  · obtain ⟨alignment, ha, hna, hba, hea⟩ := halign
    obtain ⟨offset, ho, hno, hbo, heo⟩ := hoffset
    exact .of_immediate p.inbounds hbyte p.pos (.memory opcode operation arg hrow hea heo)
      ((show BytesAt data st.pos alignment middle from ⟨ha, hna, hba⟩).append ⟨ho, hno, hbo⟩)
  · simp [hc, ctrls]

end Itasca.Wasm1
