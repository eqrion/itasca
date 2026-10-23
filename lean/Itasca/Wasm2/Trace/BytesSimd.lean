import Itasca.Wasm2.Trace.BytesBulk
import Itasca.Wasm2.Simd.Sound

/-!
# Byte provenance for SIMD callbacks

Independent byte provenance for each SIMD class dispatched by `code.step_simd` (`simd_pure`,
`simd_lane`, `simd_const`, `simd_shuffle`, `simd_memory`, `simd_memory_lane`), assembled in
`simd` for every ordinary return. `fixed_trace` is the shared case where the operand checker
fails after a decoded immediate.
-/

open Aeneas Aeneas.Std
namespace Itasca.Wasm2.CallbackBytes
open VisitorTrace CallbackTrace

/-- The operand checker preserves the cursor even when its operand check fails. -/
theorem fixed_trace {data env profile locals index st} (p : Pending data env profile locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (action : Action) (token : Token)
    (haction : actionToken action [] = some token) (hbranch : action.opcode ≠ some 0x0E#u8)
    (inputs : List types.ValueType) (output : Option types.ValueType) (pos : Usize)
    (hsize : st.core.vals.val.length < Usize.max) (hencoded : At data p.start token pos)
    (v : V) (result : core.result.Result Unit error.OpError) (final : code.OpIterState) (v' : V)
    (run : CoreVisitor.run (Simd.readFixed {st.core with pos := pos} inputs output)
      (fun v s _ => invoke visitor v (.op s action)) v = .ok (result, final, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      CallbackTrace.StepTrace data p.start observations result final := by
  apply CallbackTrace.run_step_trace data p.start _ visitor observe records (fun _ => action) ?_ v result final v' run
  intro s a hr
  obtain ⟨_, outer, _, _, base, _, ctrls, _, stack⟩ := p.opened
  have spec := Simd.readFixed.segment {st.core with pos := pos} inputs output outer p.current.vals stack
    (by simp [Control.base, ctrls, base]) hsize
  rw [hr, WP.spec_ok] at spec
  dsimp only at spec
  exact ⟨token, haction, hbranch, by simpa [spec.2.1] using hencoded⟩

theorem simd_pure {data env profile locals index st} (p : Pending data env profile locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (subopcode : U32) (op : Simd.Operation)
    (hmap : Simd.pureMeaning subopcode.val = some op) (pos : Usize)
    (hsize : st.core.vals.val.length < Usize.max)
    (hencoded : At data p.start (.plain op.instruction) pos)
    (v : V) (result : core.result.Result Unit error.OpError) (final : code.OpIterState) (v' : V)
    (run : Simd.subStep visitor {st.core with pos := pos} data env subopcode v = .ok (result, final, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      CallbackTrace.StepTrace data p.start observations result final := by
  rw [Simd.subStep.pure _ _ _ _ _ _ _ hmap, Simd.signature_fixed] at run
  exact fixed_trace p visitor observe records (.simd subopcode) (.plain op.instruction)
    (by simp [actionToken, Action.token, hmap]) (by simp [Action.opcode])
    _ _ pos hsize hencoded v result final v' run

theorem simd_lane {data env profile locals index st} (p : Pending data env profile locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (subopcode : U32) (op : Simd.LaneOperation)
    (hmap : Simd.laneMeaning subopcode.val = some op) (pos : Usize)
    (hsize : st.core.vals.val.length < Usize.max)
    (hencoded : ∀ lane next, Wasm1.BytesAt data pos [lane] next →
      At data p.start (.plain (op.instruction (.mk_uN lane.val))) next)
    (v : V) (result : core.result.Result Unit error.OpError) (final : code.OpIterState) (v' : V)
    (run : Simd.subStep visitor {st.core with pos := pos} data env subopcode v = .ok (result, final, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      CallbackTrace.StepTrace data p.start observations result final := by
  rw [Simd.subStep.lane _ _ _ _ _ _ _ hmap, Simd.lane_fixed] at run
  obtain ⟨⟨res, decoded⟩, hd, hc, hvals, hlane⟩ := WP.spec_imp_exists
    (Simd.take_lane_spec {st.core with pos := pos} data op.runtime.2.1)
  have hstate : decoded = {st.core with pos := decoded.pos} :=
    Simd.state_of_stacks decoded st.core hvals hc
  simp only [Simd.laneReader, hd, bind_ok, Std.uncurry] at run
  cases res with
  | Err e =>
    simp [CoreVisitor.run, bind_ok, Std.uncurry,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      Result.ok.injEq, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl, rfl⟩ := run
    exact ⟨[], by simp, .silent _ _ (Outcomes.empty _)⟩
  | Ok lane =>
    obtain ⟨_, hbytes⟩ := hlane lane rfl
    rw [hstate, Simd.carryFixed.run] at run
    exact fixed_trace p visitor observe records (.simd_lane subopcode lane)
      (.plain (op.instruction (.mk_uN lane.val)))
      (by simp [actionToken, Action.token, hmap]) (by simp [Action.opcode])
      _ _ decoded.pos hsize (hencoded lane decoded.pos hbytes) v result final v' run

theorem simd_const {data env profile locals index st} (p : Pending data env profile locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (pos : Usize)
    (hsize : st.core.vals.val.length < Usize.max)
    (hencoded : ∀ low high next, Simd.BitsDecoded data pos low high next →
      At data p.start (.plain (Simd.vectorConstant low high)) next)
    (v : V) (result : core.result.Result Unit error.OpError) (final : code.OpIterState) (v' : V)
    (run : Simd.subStep visitor {st.core with pos := pos} data env 12#u32 v = .ok (result, final, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      CallbackTrace.StepTrace data p.start observations result final := by
  rw [Simd.subStep.constant, Simd.const_fixed] at run
  obtain ⟨⟨res, decoded⟩, hd, hc, hvals, hbits⟩ := WP.spec_imp_exists
    (Simd.take_bits_spec {st.core with pos := pos} data)
  have hstate : decoded = {st.core with pos := decoded.pos} :=
    Simd.state_of_stacks decoded st.core hvals hc
  simp only [Simd.constReader, hd, bind_ok, Std.uncurry] at run
  cases res with
  | Err e =>
    simp [CoreVisitor.run, bind_ok, Std.uncurry,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      Result.ok.injEq, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl, rfl⟩ := run
    exact ⟨[], by simp, .silent _ _ (Outcomes.empty _)⟩
  | Ok pair =>
    obtain ⟨low, high⟩ := pair
    rw [hstate, Simd.carryFixed.run] at run
    exact fixed_trace p visitor observe records (.simd_const low high)
      (.plain (Simd.vectorConstant low high)) rfl (by simp [Action.opcode])
      _ _ decoded.pos hsize (hencoded low high decoded.pos (hbits low high rfl)) v result final v' run

theorem simd_shuffle {data env profile locals index st} (p : Pending data env profile locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (pos : Usize) (hpos : pos.val ≤ data.length)
    (hsize : st.core.vals.val.length < Usize.max)
    (hencoded : ∀ low high next, Simd.BitsDecoded data pos low high next →
      At data p.start (.plain (Simd.shuffle low high)) next)
    (v : V) (result : core.result.Result Unit error.OpError) (final : code.OpIterState) (v' : V)
    (run : Simd.subStep visitor {st.core with pos := pos} data env 13#u32 v = .ok (result, final, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      CallbackTrace.StepTrace data p.start observations result final := by
  rw [Simd.subStep.shuffle] at run
  apply CallbackTrace.run_step_trace data p.start _ visitor observe records (fun (a : U64 × U64) => .simd_shuffle a.1 a.2) ?_ v result final v' run
  intro s a hr
  obtain ⟨low, high⟩ := a
  obtain ⟨_, outer, _, _, base, _, ctrls, _, stack⟩ := p.opened
  have spec := Simd.shuffle_segment {st.core with pos := pos} data outer p.current.vals stack
    (by simp [Control.base, ctrls, base]) hsize hpos
  rw [hr, WP.spec_ok] at spec
  obtain ⟨_, _, _, hbits, _⟩ := spec low high rfl
  exact ⟨.plain (Simd.shuffle low high), rfl, by simp [Action.opcode], hencoded low high s.pos hbits⟩

theorem simd_memory {data env profile locals index st} (p : Pending data env profile locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (subopcode : U32) (op : Simd.MemoryOperation)
    (hmap : Simd.memoryMeaning subopcode.val = some op) (hfull : op.laneCount = 0) (pos : Usize)
    (hsize : st.core.vals.val.length < Usize.max)
    (hencoded : ∀ arg middle next, Leb128.Decoded data pos arg.align middle →
      Leb128.Decoded data middle arg.offset next →
      At data p.start (.plain (op.instruction (MemoryMeaning.memArg arg) (.mk_uN 0))) next)
    (v : V) (result : core.result.Result Unit error.OpError) (final : code.OpIterState) (v' : V)
    (run : Simd.subStep visitor {st.core with pos := pos} data env subopcode v = .ok (result, final, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      CallbackTrace.StepTrace data p.start observations result final := by
  rw [Simd.subStep.memory _ _ _ _ _ _ _ hmap hfull, Simd.full_memory_fixed] at run
  obtain ⟨⟨res, decoded⟩, hd, hvals, hc, harg⟩ := WP.spec_imp_exists
    (code.read_memarg.spec {st.core with pos := pos} data)
  have hstate : decoded = {st.core with pos := decoded.pos} :=
    Simd.state_of_stacks decoded st.core hvals hc
  simp only [Simd.fullMemoryReader, hd, bind_ok, Std.uncurry] at run
  cases res with
  | Err e =>
    simp [CoreVisitor.run, bind_ok, Std.uncurry,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      Result.ok.injEq, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl, rfl⟩ := run
    exact ⟨[], by simp, .silent _ _ (Outcomes.empty _)⟩
  | Ok arg =>
    obtain ⟨middle, halign, hoffset⟩ := harg
    obtain ⟨res, hcheck, _⟩ := WP.spec_imp_exists
      (code.check_memory_and_alignment.spec env arg op.runtime.1)
    dsimp only at run
    rw [hcheck] at run
    simp only [bind_ok] at run
    cases res with
    | Err e =>
      simp [CoreVisitor.run, bind_ok, Std.uncurry,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        Result.ok.injEq, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl, rfl⟩ := run
      exact ⟨[], by simp, .silent _ _ (Outcomes.empty _)⟩
    | Ok u =>
      rw [hstate, Simd.carryFixed.run] at run
      exact fixed_trace p visitor observe records (.simd_memory subopcode arg)
        (.plain (op.instruction (MemoryMeaning.memArg arg) (.mk_uN 0)))
        (by simp [actionToken, Action.token, hmap]) (by simp [Action.opcode])
        _ _ decoded.pos hsize (hencoded arg middle decoded.pos halign hoffset) v result final v' run

theorem simd_memory_lane {data env profile locals index st} (p : Pending data env profile locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (subopcode : U32) (op : Simd.MemoryOperation)
    (hmap : Simd.memoryMeaning subopcode.val = some op) (hlaned : op.laneCount ≠ 0) (pos : Usize)
    (hsize : st.core.vals.val.length < Usize.max)
    (hencoded : ∀ arg middle ending lane next, Leb128.Decoded data pos arg.align middle →
      Leb128.Decoded data middle arg.offset ending → Wasm1.BytesAt data ending [lane] next →
      At data p.start (.plain (op.instruction (MemoryMeaning.memArg arg) (.mk_uN lane.val))) next)
    (v : V) (result : core.result.Result Unit error.OpError) (final : code.OpIterState) (v' : V)
    (run : Simd.subStep visitor {st.core with pos := pos} data env subopcode v = .ok (result, final, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      CallbackTrace.StepTrace data p.start observations result final := by
  rw [Simd.subStep.memoryLane _ _ _ _ _ _ _ hmap hlaned, Simd.memory_lane_fixed] at run
  obtain ⟨⟨res, decoded⟩, hd, hvals, hc, harg⟩ := WP.spec_imp_exists
    (code.read_memarg.spec {st.core with pos := pos} data)
  simp only [Simd.memoryLaneReader, hd, bind_ok, Std.uncurry] at run
  cases res with
  | Err e =>
    simp [CoreVisitor.run, bind_ok, Std.uncurry,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      Result.ok.injEq, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl, rfl⟩ := run
    exact ⟨[], by simp, .silent _ _ (Outcomes.empty _)⟩
  | Ok arg =>
    obtain ⟨middle, halign, hoffset⟩ := harg
    obtain ⟨⟨res, laned⟩, hd2, hc2, hvals2, hlane⟩ := WP.spec_imp_exists
      (Simd.take_lane_spec decoded data op.runtime.2.2)
    simp only [hd2, bind_ok, Std.uncurry] at run
    cases res with
    | Err e =>
      simp [CoreVisitor.run, bind_ok, Std.uncurry,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        Result.ok.injEq, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl, rfl⟩ := run
      exact ⟨[], by simp, .silent _ _ (Outcomes.empty _)⟩
    | Ok lane =>
      obtain ⟨_, hbytes⟩ := hlane lane rfl
      have hstate : laned = {st.core with pos := laned.pos} :=
        Simd.state_of_stacks laned st.core (hvals2.trans hvals) (hc2.trans hc)
      obtain ⟨res, hcheck, _⟩ := WP.spec_imp_exists
        (code.check_memory_and_alignment.spec env arg op.runtime.1)
      dsimp only at run
      rw [hcheck] at run
      simp only [bind_ok] at run
      cases res with
      | Err e =>
        simp [CoreVisitor.run, bind_ok, Std.uncurry,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
          Result.ok.injEq, Prod.mk.injEq] at run
        obtain ⟨rfl, rfl, rfl⟩ := run
        exact ⟨[], by simp, .silent _ _ (Outcomes.empty _)⟩
      | Ok u =>
        rw [hstate, Simd.carryFixed.run] at run
        exact fixed_trace p visitor observe records (.simd_memory_lane subopcode arg lane)
          (.plain (op.instruction (MemoryMeaning.memArg arg) (.mk_uN lane.val)))
          (by simp [actionToken, Action.token, hmap]) (by simp [Action.opcode])
          _ _ laned.pos hsize (hencoded arg middle decoded.pos lane laned.pos halign hoffset hbytes)
          v result final v' run

/-- Every ordinary SIMD dispatcher return has an exact independent byte trace. -/
theorem simd {data env profile locals index st} (p : Pending data env profile locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (hsize : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = 0xFD#u8) :
    StepRecords p visitor observe ctx 0xFD#u8 := by
  intro v result final v' run
  rw [code.step_wasm2.simd, code.step_simd.eq_runs] at run
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
  simp only [Simd.prefixStep, hr, bind_ok] at run
  cases r with
  | Err e =>
    simp only [Result.ok.injEq, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl, rfl⟩ := run
    exact ⟨[], by simp, .silent _ _ (Outcomes.empty _)⟩
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
      apply simd_const p visitor observe records next hsize ?_ v result final v' run
      intro low high ending hbits
      obtain ⟨lower, upper, hlo, hhi, hspan⟩ := hbits
      exact henc _ _ _ (.constant low high hlo hhi) hspan
    by_cases hshuffle : subopcode = 13#u32
    · subst subopcode
      apply simd_shuffle p visitor observe records next hb hsize ?_ v result final v' run
      intro low high ending hbits
      obtain ⟨lower, upper, hlo, hhi, hspan⟩ := hbits
      exact henc _ _ _ (.shuffle low high hlo hhi) hspan
    cases hp : Simd.pureMeaning subopcode.val with
    | some op =>
      exact simd_pure p visitor observe records subopcode op hp next hsize
        (henc _ _ _ (.pure subopcode op hp) (Wasm1.BytesAt.nil data next hb)) v result final v' run
    | none =>
      cases hl : Simd.laneMeaning subopcode.val with
      | some op =>
        apply simd_lane p visitor observe records subopcode op hl next hsize ?_ v result final v' run
        intro lane ending hspan
        exact henc _ _ _ (.lane subopcode op lane hl) hspan
      | none =>
        cases hm : Simd.memoryMeaning subopcode.val with
        | some op =>
          by_cases hfull : op.laneCount = 0
          · apply simd_memory p visitor observe records subopcode op hm hfull next hsize ?_ v result final v' run
            intro arg middle ending halign hoffset
            obtain ⟨alignment, ha1, ha2, ha3, ha4⟩ := halign
            obtain ⟨offset, ho1, ho2, ho3, ho4⟩ := hoffset
            exact henc _ _ _ (.memory subopcode op arg hm hfull ha4 ho4)
              ((show Wasm1.BytesAt data next alignment middle from ⟨ha1, ha2, ha3⟩).append ⟨ho1, ho2, ho3⟩)
          · apply simd_memory_lane p visitor observe records subopcode op hm hfull next hsize ?_ v result final v' run
            intro arg middle ending lane ending' halign hoffset hspan
            obtain ⟨alignment, ha1, ha2, ha3, ha4⟩ := halign
            obtain ⟨offset, ho1, ho2, ho3, ho4⟩ := hoffset
            exact henc _ _ _ (.memoryLane subopcode op arg lane hm hfull ha4 ho4)
              (((show Wasm1.BytesAt data next alignment middle from ⟨ha1, ha2, ha3⟩).append
                ⟨ho1, ho2, ho3⟩).append hspan)
        | none =>
          simp only [Simd.subStep, Simd.pure_table, Simd.lane_table, Simd.memory_table,
            hp, hl, hm, Option.map_none, bind_ok] at run
          split at run
          · exact False.elim (hconstant (by with_unfolding_all rfl))
          · exact False.elim (hshuffle (by with_unfolding_all rfl))
          · simp only [Result.ok.injEq, Prod.mk.injEq] at run
            obtain ⟨rfl, rfl, rfl⟩ := run
            exact ⟨[], by simp, .silent _ _ (Outcomes.empty _)⟩

end Itasca.Wasm2.CallbackBytes
