import Itasca.WasmStepScalar
import Itasca.Wasm1LeafProfile
import Itasca.Wasm1Invariant
import Itasca.ScalarConst
import Itasca.AllNumeric
import Itasca.Select

open Aeneas Aeneas.Std

namespace Itasca.Wasm1Sound

open Wasm

/-- NOP accepts arbitrary unread suffixes and records its opcode byte. -/
theorem Pending.step_nop {data env ctx bt st}
    (p : Pending data env ctx bt st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_NOP) :
    code.step visitor st data env ctx code.OP_NOP v ⦃ r => r.1 = .Ok () → p.After r.2.1 ⦄ := by
  apply WP.spec_mono (code.step_nop.total visitor st data env ctx v hvisitor.toCore)
  intro r hr _
  rw [hr]
  obtain ⟨_, outer, _, _, hbase, _, hc, hv⟩ := p.opened
  apply p.append_simple st .NOP p.current.ctrl.polymorphic_base p.current.vals .instr_case_0
    (.no_immediate p.inbounds (by simpa [global_simps] using hbyte) p.pos .nop)
    (fun C hC h => h.nop hC) _ _ (by omega)
  · simpa using hc
  · simp [hv, hbase]

/-- UNREACHABLE trims the current frame and records the exact byte. -/
theorem Pending.step_unreachable {data env ctx bt st}
    (p : Pending data env ctx bt st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_UNREACHABLE) :
    code.step visitor st data env ctx code.OP_UNREACHABLE v ⦃ r => r.1 = .Ok () → p.After r.2.1 ⦄ := by
  refine WP.spec_mono (code.step_unreachable.of_read visitor st data env ctx v
    (fun _ => True) (fun _ s => p.After s) ?_ hvisitor.toCore) ?_
  · obtain ⟨_, outer, _, _, hbase, _, hc, hv⟩ := p.opened
    obtain ⟨s, hr, hsvals, _, hsctrls, hspos⟩ := WP.spec_imp_exists
      (code.mark_unreachable.spec st (p.parents.map Wasm1Frames.Saved.ctrl) p.current.ctrl hc
        (by simp [hbase, hv]))
    have encoded : At data p.start (.plain .UNREACHABLE) s.pos :=
      .no_immediate p.inbounds (by simpa [global_simps] using hbyte)
        (by simpa [hspos] using p.pos) .unreachable
    have hafter := p.append_simple s .UNREACHABLE true [] .instr_case_1 encoded
      (fun C hC h => h.unreachable hC) hsctrls (by simpa using hsvals) (by simp)
    simp only [code.read_unreachable, hr, bind_ok, WP.spec_ok]
    exact ⟨trivial, fun _ _ => hafter⟩
  · intro r hr hok
    exact (hr.2 hok).choose_spec

/-- DROP covers concrete and polymorphic operands, and may reject an empty stack. -/
theorem Pending.step_drop {data env ctx bt st}
    (p : Pending data env ctx bt st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_DROP) :
    code.step visitor st data env ctx code.OP_DROP v ⦃ r => r.1 = .Ok () → p.After r.2.1 ⦄ := by
  refine WP.spec_mono (code.step_drop.of_read visitor st data env ctx v
    (fun _ => True) (fun _ s => p.After s) ?_ hvisitor.toCore) ?_
  · obtain ⟨_, outer, _, _, hbase, _, hctrls, hstack⟩ := p.opened
    have hb : (Control.base st).val = outer.length := by simp [Control.base, hctrls, hbase]
    have hpoly : Control.polymorphic st = p.current.ctrl.polymorphic_base := by
      simp [Control.polymorphic, hctrls]
    change code.pop_stack_type st ⦃ _ ⦄
    apply WP.spec_mono (code.pop_stack_type.segment st outer p.current.vals hstack hb)
    rintro ⟨res, s⟩ ⟨hc, hp, rest, hv, hout⟩
    dsimp only at hc hp hv hout
    refine ⟨trivial, ?_⟩
    intro t hok
    dsimp only at hok ⊢
    subst res
    change StackSemantics.Popped (Control.polymorphic st) p.current.vals t rest at hout
    rw [hpoly] at hout
    have encoded : At data p.start (.plain .DROP) s.pos :=
      .no_immediate p.inbounds (by simpa [global_simps] using hbyte)
        (by simpa [hp] using p.pos) .drop
    apply p.append_simple s .DROP p.current.ctrl.polymorphic_base rest .instr_case_2 encoded
      (fun C hC h => hout.prefix_drop C hC p.current.ops h) _ _
      (by have := hout.length; omega)
    · simpa [hc] using hctrls
    · simpa [hstack, hbase] using hv
  · intro r hr hok
    exact (hr.2 hok).choose_spec

end Itasca.Wasm1Sound

namespace Itasca.Wasm1Sound

open Wasm

/-- The i32 constant step terminates on arbitrary immediate bytes and preserves the invariant on success. -/
theorem Pending.step_i32Const {data env ctx bt st}
    (p : Pending data env ctx bt st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_I32_CONST) :
    code.step visitor st data env ctx code.OP_I32_CONST v ⦃ r => r.1 = .Ok () → p.After r.2.1 ⦄ := by
  refine WP.spec_mono (code.step_i32_const.of_read visitor st data env ctx v
    (fun _ => True) (fun _ s => p.After s) ?_ hvisitor.toCore) ?_
  · apply WP.spec_mono (code.read_i32_const.spec st data (by have := p.val_capacity; omega))
    rintro ⟨res, s⟩ ⟨hc, hout⟩
    dsimp only at hc hout
    refine ⟨trivial, ?_⟩
    intro value hok
    dsimp only at hok ⊢
    subst res
    obtain ⟨hd, hv⟩ := hout
    obtain ⟨_, outer, _, _, hbase, _, hctrls, hstack⟩ := p.opened
    have encoded : At data p.start (.plain (Core.i32Const value)) s.pos :=
      .of_s32 value p.inbounds (by simpa [global_simps] using hbyte) p.pos hd
    apply p.append_simple s (Core.i32Const value) p.current.ctrl.polymorphic_base
      (p.current.vals ++ [.Val .I32]) (Core.i32Const_wf value) encoded
      (fun C hC h => h.i32Const hC value) _ _ (by simp)
    · simpa [hc] using hctrls
    · simpa [hstack, hbase, List.append_assoc] using hv
  · intro r hr hok
    exact (hr.2 hok).choose_spec

/-- The i64 constant step terminates on arbitrary immediate bytes and preserves the invariant on success. -/
theorem Pending.step_i64Const {data env ctx bt st}
    (p : Pending data env ctx bt st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_I64_CONST) :
    code.step visitor st data env ctx code.OP_I64_CONST v ⦃ r => r.1 = .Ok () → p.After r.2.1 ⦄ := by
  refine WP.spec_mono (code.step_i64_const.of_read visitor st data env ctx v
    (fun _ => True) (fun _ s => p.After s) ?_ (hvisitor.on_i64_const v)) ?_
  · apply WP.spec_mono (code.read_i64_const.spec st data (by have := p.val_capacity; omega))
    rintro ⟨res, s⟩ ⟨hc, hout⟩
    dsimp only at hc hout
    refine ⟨trivial, ?_⟩
    intro value hok
    dsimp only at hok ⊢
    subst res
    obtain ⟨hd, hv⟩ := hout
    obtain ⟨_, outer, _, _, hbase, _, hctrls, hstack⟩ := p.opened
    have encoded : At data p.start (.plain (ScalarConst.i64 value)) s.pos :=
      .of_s64 value p.inbounds (by simpa [global_simps] using hbyte) p.pos hd
    apply p.append_simple s (ScalarConst.i64 value) p.current.ctrl.polymorphic_base
      (p.current.vals ++ [.Val .I64]) (ScalarConst.i64_wf value) encoded
      (fun C hC h => h.i64Const hC value) _ _ (by simp)
    · simpa [hc] using hctrls
    · simpa [hstack, hbase, List.append_assoc] using hv
  · intro r hr hok
    exact (hr.2 hok).choose_spec

/-- The f32 constant step terminates on arbitrary immediate bytes and preserves the invariant on success. -/
theorem Pending.step_f32Const {data env ctx bt st}
    (p : Pending data env ctx bt st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_F32_CONST) :
    code.step visitor st data env ctx code.OP_F32_CONST v ⦃ r => r.1 = .Ok () → p.After r.2.1 ⦄ := by
  refine WP.spec_mono (code.step_f32_const.of_read visitor st data env ctx v
    (fun _ => True) (fun _ s => p.After s) ?_ (hvisitor.on_f32_const v)) ?_
  · apply WP.spec_mono (code.read_f32_const.spec st data (by have := p.val_capacity; omega))
    rintro ⟨res, s⟩ ⟨hc, hout⟩
    dsimp only at hc hout
    refine ⟨trivial, ?_⟩
    intro value hok
    dsimp only at hok ⊢
    subst res
    obtain ⟨hd, hv⟩ := hout
    obtain ⟨_, outer, _, _, hbase, _, hctrls, hstack⟩ := p.opened
    have encoded : At data p.start (.plain (ScalarConst.f32 value)) s.pos :=
      .of_f32 value p.inbounds (by simpa [global_simps] using hbyte) p.pos hd
    apply p.append_simple s (ScalarConst.f32 value) p.current.ctrl.polymorphic_base
      (p.current.vals ++ [.Val .F32]) (ScalarConst.f32_wf value) encoded
      (fun C hC h => h.f32Const hC value) _ _ (by simp)
    · simpa [hc] using hctrls
    · simpa [hstack, hbase, List.append_assoc] using hv
  · intro r hr hok
    exact (hr.2 hok).choose_spec

/-- The f64 constant step terminates on arbitrary immediate bytes and preserves the invariant on success. -/
theorem Pending.step_f64Const {data env ctx bt st}
    (p : Pending data env ctx bt st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_F64_CONST) :
    code.step visitor st data env ctx code.OP_F64_CONST v ⦃ r => r.1 = .Ok () → p.After r.2.1 ⦄ := by
  refine WP.spec_mono (code.step_f64_const.of_read visitor st data env ctx v
    (fun _ => True) (fun _ s => p.After s) ?_ (hvisitor.on_f64_const v)) ?_
  · apply WP.spec_mono (code.read_f64_const.spec st data (by have := p.val_capacity; omega))
    rintro ⟨res, s⟩ ⟨hc, hout⟩
    dsimp only at hc hout
    refine ⟨trivial, ?_⟩
    intro value hok
    dsimp only at hok ⊢
    subst res
    obtain ⟨hd, hv⟩ := hout
    obtain ⟨_, outer, _, _, hbase, _, hctrls, hstack⟩ := p.opened
    have encoded : At data p.start (.plain (ScalarConst.f64 value)) s.pos :=
      .of_f64 value p.inbounds (by simpa [global_simps] using hbyte) p.pos hd
    apply p.append_simple s (ScalarConst.f64 value) p.current.ctrl.polymorphic_base
      (p.current.vals ++ [.Val .F64]) (ScalarConst.f64_wf value) encoded
      (fun C hC h => h.f64Const hC value) _ _ (by simp)
    · simpa [hc] using hctrls
    · simpa [hstack, hbase, List.append_assoc] using hv
  · intro r hr hok
    exact (hr.2 hok).choose_spec

end Itasca.Wasm1Sound

namespace Itasca.Wasm1Sound

open Wasm

/-- Every numeric opcode extends the generated typing derivation under the current frame context. -/
theorem Pending.step_numeric_mapped {data env ctx bt st}
    (p : Pending data env ctx bt st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V) (opcode : U8) (op : Numeric.Operation)
    (hbyte : data.val[p.start.val]'p.inbounds = opcode)
    (hmap : Numeric.opcodeMeaning opcode = some op) :
    code.step visitor st data env ctx opcode v ⦃ r => r.1 = .Ok () → p.After r.2.1 ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, stack⟩ := id p.opened
  have hC := Wasm1Frames.enter_wf C (spine.context_wf (EnvTranslation.context_wf env ctx))
    p.current.form p.current.ctrl.block_type
  have hbase : (Control.base st).val = outer.length := by simp [Control.base, ctrls, base]
  have hpoly : Control.polymorphic st = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  apply WP.spec_mono (code.step.numeric_prefix visitor st data env ctx opcode op outer
    p.current.vals v _ hC p.current.ops (by simpa [hpoly] using typed) hmap stack hbase
    (by have := p.val_capacity; omega) hvisitor)
  rintro ⟨res, s, v'⟩ ⟨hc, hp, after, hv, hlen, hout⟩ hok
  dsimp only at hc hp hv hlen hout hok ⊢
  have encoded : At data p.start (.plain op.instruction) s.pos :=
    .no_immediate p.inbounds hbyte (by simpa [hp] using p.pos) (.numeric opcode op hmap)
  apply p.append_result C outer spine header base ctrls stack s op.instruction
    p.current.ctrl.polymorphic_base after op.wellFormed encoded _ _ hv hlen (Numeric.opcode_profile opcode op hmap _)
  · simpa [hpoly] using hout hok
  · simpa [hc] using ctrls

/-- Unmapped high opcodes terminate with rejection; mapped scalar opcodes preserve the invariant. -/
theorem Pending.step_numeric {data env ctx bt st}
    (p : Pending data env ctx bt st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V) (opcode : U8)
    (hbyte : data.val[p.start.val]'p.inbounds = opcode) (hlow : 0x45 ≤ opcode.val) :
    code.step visitor st data env ctx opcode v ⦃ r => r.1 = .Ok () → p.After r.2.1 ⦄ := by
  cases hm : Numeric.opcodeMeaning opcode with
  | none =>
    rw [code.step.numeric_dispatch visitor st data env ctx opcode v hlow,
      code.step_numeric.unrecognized visitor st opcode v hm]
    simp
  | some op => exact p.step_numeric_mapped visitor hvisitor v opcode op hbyte hm

/-- SELECT preserves its joined concrete/bottom result and exact opcode provenance. -/
theorem Pending.step_select {data env ctx bt st}
    (p : Pending data env ctx bt st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : FullVisitor.Total visitor) (v : V)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_SELECT) :
    code.step visitor st data env ctx code.OP_SELECT v ⦃ r => r.1 = .Ok () → p.After r.2.1 ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, stack⟩ := id p.opened
  have hC := Wasm1Frames.enter_wf C (spine.context_wf (EnvTranslation.context_wf env ctx))
    p.current.form p.current.ctrl.block_type
  have hbase : (Control.base st).val = outer.length := by simp [Control.base, ctrls, base]
  have hpoly : Control.polymorphic st = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  apply WP.spec_mono (code.step_select.prefix visitor st data env ctx outer
    p.current.vals v _ hC p.current.ops (by simpa [hpoly] using typed) stack hbase
    (by have := p.val_capacity; omega) hvisitor)
  rintro ⟨res, s, v'⟩ ⟨hc, hp, after, hv, hlen, hout⟩ hok
  dsimp only at hc hp hv hlen hout hok ⊢
  have encoded : At data p.start (.plain (.SELECT none)) s.pos :=
    .no_immediate p.inbounds (by simpa [global_simps] using hbyte)
      (by simpa [hp] using p.pos) .select
  apply p.append_result C outer spine header base ctrls stack s (.SELECT none)
    p.current.ctrl.polymorphic_base after (.instr_case_3 _) encoded _ _ hv hlen
  · simpa [hpoly] using hout hok
  · simpa [hc] using ctrls

end Itasca.Wasm1Sound
