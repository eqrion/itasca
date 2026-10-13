import Itasca.Wasm2.Simd.Shuffle
import Itasca.Wasm2.Invariant
import Itasca.Wasm2.Simd.Visitor
import Itasca.Wasm2.Simd.LaneReaders
import Itasca.Wasm2.Simd.Decode
import Itasca.Wasm2.Simd.Dispatch
import Itasca.Binary.Wasm2.SimdBitsMeaning
import Itasca.Wasm2.Simd.MemoryReaders

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

private theorem lane_wf (lane : U8) : wf_uN 8 (.mk_uN lane.val) := by
  constructor
  scalar_tac

/-- A fixed operand effect extends the independently typed prefix in the active frame. -/
theorem Pending.fixed {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (v : V)
    (inputs : List types.ValueType) (output : Option types.ValueType) (op : instr)
    (hw : wf_instr op)
    (hdecl : DeclaredReferences.Instruction (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) op)
    (ht : ∀ C, wf_context C → EnvTranslation.Matches env ⟨locals, p.ft.results⟩ C → Instr_ok C op
      (.mk_functype (.mk_list (Simd.inputTypes inputs)) (.mk_list (Simd.outputTypes output))))
    (pos : Usize) (hsize : st.core.vals.val.length < Usize.max)
    (hook : V → code.OpIterState → Unit → Result (core.result.Result Unit error.VisitError × V))
    (hhook : ∀ s a, ∃ reply v', hook v s a = .ok (reply, v'))
    (hencoded : At data p.start (.plain op) pos) :
    CoreVisitor.run (Simd.readFixed {st.core with pos := pos} inputs output) hook v ⦃ r =>
      r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, stack⟩ := id p.opened
  let decoded := {st.core with pos := pos}
  have hC := Frames.enter_wf C (spine.context_wf (EnvTranslation.context_wf env ⟨locals, p.ft.results⟩))
    p.current.form p.current.ins p.current.outs
  have hmatches : EnvTranslation.Matches env ⟨locals, p.ft.results⟩
      (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (EnvTranslation.Matches.root env ⟨locals, p.ft.results⟩)).enter _
  have hbase : (Control.base decoded).val = outer.length := by simp [decoded, Control.base, ctrls, base]
  have hpoly : Control.polymorphic decoded = p.current.ctrl.polymorphic_base := by
    simp [decoded, Control.polymorphic, ctrls]
  apply WP.spec_mono (CoreVisitor.run.spec _ hook v (fun _ => True)
    (fun _ s => p.After {st with core := s}) ?_ hhook)
  · intro r hr hok
    exact (hr.2 hok).choose_spec
  · apply WP.spec_mono (Simd.readFixed.segment decoded inputs output outer p.current.vals stack hbase hsize)
    rintro ⟨res, s⟩ ⟨hc, hp, after, hv, hlen, hout⟩
    dsimp only at hc hp hv hlen hout
    refine ⟨trivial, ?_⟩
    intro u hu
    cases u
    dsimp only at hu
    subst res
    have htyped := (hout rfl).multi_prefix _ hC _ p.current.ops op
      (by simpa [hpoly] using typed) hw (ht _ hC hmatches)
    apply p.append_result C outer spine header base {st with core := s} op
      p.current.ctrl.polymorphic_base after hw
      (by simpa [hp, decoded] using hencoded) (by simpa [hpoly] using htyped) ?_ ?_ hv hdecl
    · simpa [hc, decoded] using ctrls
    · simpa [code.BodyState.blocks_eq_of_ctrls (show s.ctrls = st.core.ctrls from hc)] using blocks

theorem Pending.simd_pure {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V) (v : V)
    (hv : FullVisitor.Total visitor) (subopcode : U32) (op : Simd.Operation)
    (hmap : Simd.pureMeaning subopcode.val = some op) (pos : Usize)
    (hsize : st.core.vals.val.length < Usize.max)
    (hencoded : At data p.start (.plain op.instruction) pos) :
    Simd.subStep visitor {st.core with pos := pos} data env subopcode v ⦃ r =>
      r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  simp only [Simd.subStep, Simd.pure_table, hmap, Option.map_some, bind_ok]
  rw [Simd.signature_fixed]
  apply p.fixed v op.signature.popTypes (some op.signature.output) op.instruction op.wellFormed (op.declared _)
    (fun C hC _ => by simpa [Simd.Signature.inputs_pop, Simd.Signature.outputs_pop] using op.typed C hC)
    pos hsize _ (fun s _ => hv.on_simd v s subopcode) hencoded

theorem Pending.simd_lane {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V) (v : V)
    (hv : FullVisitor.Total visitor) (subopcode : U32) (op : Simd.LaneOperation)
    (hmap : Simd.laneMeaning subopcode.val = some op) (pos : Usize)
    (hsize : st.core.vals.val.length < Usize.max)
    (hencoded : ∀ lane next, Wasm1.BytesAt data pos [lane] next →
      At data p.start (.plain (op.instruction (.mk_uN lane.val))) next) :
    Simd.subStep visitor {st.core with pos := pos} data env subopcode v ⦃ r =>
      r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  rw [Simd.subStep.lane _ _ _ _ _ _ _ hmap, Simd.lane_fixed]
  obtain ⟨⟨res, decoded⟩, hd, hc, hvals, hlane⟩ := WP.spec_imp_exists
    (Simd.take_lane_spec {st.core with pos := pos} data op.runtime.2.1)
  have hstate : decoded = {st.core with pos := decoded.pos} := by
    exact Simd.state_of_stacks decoded st.core hvals hc
  simp only [Simd.laneReader]
  rw [hd]
  simp only [bind_ok, Std.uncurry]
  cases res with
  | Err e => simp [CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok lane =>
    obtain ⟨hbound, hbytes⟩ := hlane lane rfl
    rw [hstate, Simd.carryFixed.run]
    apply p.fixed v (Simd.laneInputs op.runtime.1 op.replace)
      (Simd.laneOutput op.runtime.1 op.replace) (op.instruction (.mk_uN lane.val))
      (op.wellFormed _ (lane_wf lane)) (op.declared _ _)
      (fun C hC _ => ?_) decoded.pos hsize _ (fun s _ => hv.on_simd_lane v s subopcode lane)
      (hencoded lane decoded.pos hbytes)
    simpa only [Simd.LaneOperation.inputs_pop, Simd.LaneOperation.outputs_pop] using
      op.typed C (.mk_uN lane.val) hC (lane_wf lane)
        (by simpa [Simd.LaneOperation.runtime, proj_uN_0] using hbound)


theorem Pending.simd_const {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V) (v : V)
    (hv : FullVisitor.Total visitor) (pos : Usize)
    (hsize : st.core.vals.val.length < Usize.max)
    (hencoded : ∀ low high next, Simd.BitsDecoded data pos low high next →
      At data p.start (.plain (Simd.vectorConstant low high)) next) :
    Simd.subStep visitor {st.core with pos := pos} data env 12#u32 v ⦃ r =>
      r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  rw [Simd.subStep.constant, Simd.const_fixed]
  obtain ⟨⟨res, decoded⟩, hd, hc, hvals, hbits⟩ := WP.spec_imp_exists
    (Simd.take_bits_spec {st.core with pos := pos} data)
  have hstate : decoded = {st.core with pos := decoded.pos} :=
    Simd.state_of_stacks decoded st.core hvals hc
  simp only [Simd.constReader, hd, bind_ok, Std.uncurry]
  cases res with
  | Err e => simp [CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨low, high⟩ := pair
    rw [hstate, Simd.carryFixed.run]
    apply p.fixed v [] (some .V128) (Simd.vectorConstant low high)
      (Simd.vectorConstant_wf low high) (Simd.vectorConstant_declared _ low high)
      (fun C hC _ => Simd.vectorConstant_typed C low high hC)
      decoded.pos hsize _ (fun s _ => hv.on_simd_const v s low high)
      (hencoded low high decoded.pos (hbits low high rfl))


theorem Pending.simd_memory {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V) (v : V)
    (hv : FullVisitor.Total visitor) (subopcode : U32) (op : Simd.MemoryOperation)
    (hmap : Simd.memoryMeaning subopcode.val = some op) (hfull : op.laneCount = 0) (pos : Usize)
    (hsize : st.core.vals.val.length < Usize.max)
    (hencoded : ∀ arg middle next, Leb128.Decoded data pos arg.align middle →
      Leb128.Decoded data middle arg.offset next →
      At data p.start (.plain (op.instruction (MemoryMeaning.memArg arg) (.mk_uN 0))) next) :
    Simd.subStep visitor {st.core with pos := pos} data env subopcode v ⦃ r =>
      r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  rw [Simd.subStep.memory _ _ _ _ _ _ _ hmap hfull, Simd.full_memory_fixed]
  obtain ⟨⟨res, decoded⟩, hd, hvals, hc, harg⟩ := WP.spec_imp_exists
    (code.read_memarg.spec {st.core with pos := pos} data)
  have hstate : decoded = {st.core with pos := decoded.pos} :=
    Simd.state_of_stacks decoded st.core hvals hc
  simp only [Simd.fullMemoryReader, hd, bind_ok, Std.uncurry]
  cases res with
  | Err e => simp [CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok arg =>
    obtain ⟨middle, halign, hoffset⟩ := harg
    obtain ⟨res, hcheck, hc⟩ := WP.spec_imp_exists
      (code.check_memory_and_alignment.spec env arg op.runtime.1)
    dsimp only
    rw [hcheck]
    simp only [bind_ok]
    cases res with
    | Err e => simp [CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok unit =>
      rw [hstate, Simd.carryFixed.run]
      apply p.fixed v (Simd.fullMemoryInputs op.store) (Simd.memoryOutput op.store)
        (op.instruction (MemoryMeaning.memArg arg) (.mk_uN 0))
        (op.wellFormed _ _ (MemoryMeaning.memArg_wf arg) (by constructor; decide)) (op.declared _ _ _)
        (fun C hC hm => ?_) decoded.pos hsize _ (fun s _ => hv.on_simd_memory v s subopcode arg)
        (hencoded arg middle decoded.pos halign hoffset)
      simpa only [op.inputs_full hfull, Simd.MemoryOperation.outputs_pop, UScalar.ofNatCore_val_eq] using
        op.typed_runtime C env ⟨locals, p.ft.results⟩ hC hm arg 0#u8 hc.1
          (by simpa [Simd.MemoryOperation.runtime] using hc.2) (by simp [hfull])

theorem Pending.simd_memory_lane {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V) (v : V)
    (hv : FullVisitor.Total visitor) (subopcode : U32) (op : Simd.MemoryOperation)
    (hmap : Simd.memoryMeaning subopcode.val = some op) (hlaned : op.laneCount ≠ 0) (pos : Usize)
    (hsize : st.core.vals.val.length < Usize.max)
    (hencoded : ∀ arg middle ending lane next, Leb128.Decoded data pos arg.align middle →
      Leb128.Decoded data middle arg.offset ending → Wasm1.BytesAt data ending [lane] next →
      At data p.start (.plain (op.instruction (MemoryMeaning.memArg arg) (.mk_uN lane.val))) next) :
    Simd.subStep visitor {st.core with pos := pos} data env subopcode v ⦃ r =>
      r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  rw [Simd.subStep.memoryLane _ _ _ _ _ _ _ hmap hlaned, Simd.memory_lane_fixed]
  obtain ⟨⟨res, decoded⟩, hd, hvals, hc, harg⟩ := WP.spec_imp_exists
    (code.read_memarg.spec {st.core with pos := pos} data)
  simp only [Simd.memoryLaneReader, hd, bind_ok, Std.uncurry]
  cases res with
  | Err e => simp [CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok arg =>
    obtain ⟨middle, halign, hoffset⟩ := harg
    obtain ⟨⟨res, laned⟩, hd, hc2, hvals2, hlane⟩ := WP.spec_imp_exists
      (Simd.take_lane_spec decoded data op.runtime.2.2)
    simp only [hd, bind_ok, Std.uncurry]
    cases res with
    | Err e => simp [CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok lane =>
      obtain ⟨hbound, hbytes⟩ := hlane lane rfl
      have hstate : laned = {st.core with pos := laned.pos} :=
        Simd.state_of_stacks laned st.core (hvals2.trans hvals) (hc2.trans hc)
      obtain ⟨res, hcheck, hc⟩ := WP.spec_imp_exists
        (code.check_memory_and_alignment.spec env arg op.runtime.1)
      rw [hcheck]
      simp only [bind_ok]
      cases res with
      | Err e => simp [CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok unit =>
        rw [hstate, Simd.carryFixed.run]
        apply p.fixed v [.V128, .I32] (Simd.memoryOutput op.store)
          (op.instruction (MemoryMeaning.memArg arg) (.mk_uN lane.val))
          (op.wellFormed _ _ (MemoryMeaning.memArg_wf arg) (lane_wf lane)) (op.declared _ _ _)
          (fun C hC hm => ?_) laned.pos hsize _ (fun s _ => hv.on_simd_memory_lane v s subopcode arg lane)
          (hencoded arg middle decoded.pos lane laned.pos halign hoffset hbytes)
        simpa only [op.inputs_lane hlaned, Simd.MemoryOperation.outputs_pop] using
          op.typed_runtime C env ⟨locals, p.ft.results⟩ hC hm arg lane hc.1
            (by simpa [Simd.MemoryOperation.runtime] using hc.2)
            (fun _ => by simpa [Simd.MemoryOperation.runtime] using hbound)


/-- A shuffle's scanner proves the lane limits before its fixed binary stack effect. -/
theorem Pending.simd_shuffle {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V) (v : V)
    (hv : FullVisitor.Total visitor) (pos : Usize) (hpos : pos.val ≤ data.length)
    (hsize : st.core.vals.val.length < Usize.max)
    (hencoded : ∀ low high next, Simd.BitsDecoded data pos low high next →
      At data p.start (.plain (Simd.shuffle low high)) next) :
    Simd.subStep visitor {st.core with pos := pos} data env 13#u32 v ⦃ r =>
      r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  rw [Simd.subStep.shuffle]
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, stack⟩ := id p.opened
  let decoded := {st.core with pos := pos}
  have hC := Frames.enter_wf C (spine.context_wf (EnvTranslation.context_wf env ⟨locals, p.ft.results⟩))
    p.current.form p.current.ins p.current.outs
  have hbase : (Control.base decoded).val = outer.length := by simp [decoded, Control.base, ctrls, base]
  have hpoly : Control.polymorphic decoded = p.current.ctrl.polymorphic_base := by
    simp [decoded, Control.polymorphic, ctrls]
  apply WP.spec_mono (CoreVisitor.run.spec _ _ v (fun _ => True)
    (fun _ s => p.After {st with core := s}) ?_ (fun s a => hv.on_simd_shuffle v s a.1 a.2))
  · intro r hr hok
    exact (hr.2 hok).choose_spec
  · apply WP.spec_mono (Simd.shuffle_segment decoded data outer p.current.vals stack hbase hsize hpos)
    rintro ⟨res, s⟩ hpost
    refine ⟨trivial, ?_⟩
    rintro ⟨low, high⟩ hok
    obtain ⟨hc, after, hvals, hbits, hbound, heffect⟩ := hpost low high hok
    dsimp only at hc hvals hbits hbound heffect
    have htyped := heffect.multi_prefix _ hC _ p.current.ops (Simd.shuffle low high)
      (by simpa [hpoly] using typed) (Simd.shuffle_wf low high)
      (Simd.shuffle_typed _ low high hC hbound)
    apply p.append_result C outer spine header base {st with core := s} (Simd.shuffle low high)
      p.current.ctrl.polymorphic_base after (Simd.shuffle_wf low high)
      (hencoded low high s.pos hbits) (by simpa [hpoly] using htyped) ?_ ?_ hvals
      (Simd.shuffle_declared _ low high)
    · simpa [hc, decoded] using ctrls
    · simpa [code.BodyState.blocks_eq_of_ctrls (show s.ctrls = st.core.ctrls from hc)] using blocks

/-- The complete SIMD prefix dispatcher preserves the independently encoded typed body. -/
theorem Pending.simd {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hv : FullVisitor.Total visitor)
    (hsize : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = 0xFD#u8) :
    code.step_simd visitor st.core data env v ⦃ r =>
      r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  rw [code.step_simd.eq_runs]
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
  simp only [Simd.prefixStep, hr, bind_ok]
  cases r with
  | Err e => simp
  | Ok pair =>
    obtain ⟨subopcode, next⟩ := pair
    obtain ⟨prefixBytes, hs, hn, hb, he⟩ := hd
    have hprefix : Wasm1.BytesAt data st.core.pos prefixBytes next := ⟨hs, hn, hb⟩
    have henc : ∀ op bytes ending, Simd.Immediate subopcode op bytes →
        Wasm1.BytesAt data next bytes ending → At data p.start (.plain op) ending := by
      intro op bytes ending hi hbytes
      exact At.of_immediate p.inbounds hbyte p.pos (.simd subopcode he hi) (hprefix.append hbytes)
    by_cases hconstant : subopcode = 12#u32
    · subst subopcode
      apply p.simd_const visitor v hv next hsize
      intro low high ending hbits
      obtain ⟨lower, upper, hlo, hhi, hspan⟩ := hbits
      exact henc _ _ _ (.constant low high hlo hhi) hspan
    by_cases hshuffle : subopcode = 13#u32
    · subst subopcode
      apply p.simd_shuffle visitor v hv next hb hsize
      intro low high ending hbits
      obtain ⟨lower, upper, hlo, hhi, hspan⟩ := hbits
      exact henc _ _ _ (.shuffle low high hlo hhi) hspan
    cases hp : Simd.pureMeaning subopcode.val with
    | some op =>
      exact p.simd_pure visitor v hv subopcode op hp next hsize
        (henc _ _ _ (.pure subopcode op hp) (Wasm1.BytesAt.nil data next hb))
    | none =>
      cases hl : Simd.laneMeaning subopcode.val with
      | some op =>
        apply p.simd_lane visitor v hv subopcode op hl next hsize
        intro lane ending hspan
        exact henc _ _ _ (.lane subopcode op lane hl) hspan
      | none =>
        cases hm : Simd.memoryMeaning subopcode.val with
        | some op =>
          by_cases hfull : op.laneCount = 0
          · apply p.simd_memory visitor v hv subopcode op hm hfull next hsize
            intro arg middle ending halign hoffset
            obtain ⟨alignment, ha1, ha2, ha3, ha4⟩ := halign
            obtain ⟨offset, ho1, ho2, ho3, ho4⟩ := hoffset
            exact henc _ _ _ (.memory subopcode op arg hm hfull ha4 ho4)
              ((show Wasm1.BytesAt data next alignment middle from ⟨ha1, ha2, ha3⟩).append ⟨ho1, ho2, ho3⟩)
          · apply p.simd_memory_lane visitor v hv subopcode op hm hfull next hsize
            intro arg middle ending lane final halign hoffset hspan
            obtain ⟨alignment, ha1, ha2, ha3, ha4⟩ := halign
            obtain ⟨offset, ho1, ho2, ho3, ho4⟩ := hoffset
            exact henc _ _ _ (.memoryLane subopcode op arg lane hm hfull ha4 ho4)
              (((show Wasm1.BytesAt data next alignment middle from ⟨ha1, ha2, ha3⟩).append
                ⟨ho1, ho2, ho3⟩).append hspan)
        | none =>
          simp only [Simd.subStep, Simd.pure_table, Simd.lane_table, Simd.memory_table,
            hp, hl, hm, Option.map_none, bind_ok]
          split <;> simp_all
          · exact False.elim (hconstant (by with_unfolding_all rfl))
          · exact False.elim (hshuffle (by with_unfolding_all rfl))

end Itasca.Wasm2
