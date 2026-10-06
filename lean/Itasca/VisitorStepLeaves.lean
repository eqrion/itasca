import Itasca.VisitorLeafDispatch
import Itasca.VisitorSingleTrace
import Itasca.WasmInvariant

open Aeneas Aeneas.Std

namespace Itasca.VisitorTrace

theorem step_nop {data env ctx bt st} (p : Wasm.Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_NOP) :
    StepRecords p visitor observe code.OP_NOP := by
  intro v result final v' h
  rw [dispatch_nop] at h
  apply run_step_trace data p.start _ visitor observe hrecords (fun _ => .nop) ?_ v result final v' h
  intro s a hr
  have heq : st = s := by simpa using hr
  subst s
  exact ⟨.plain .NOP, rfl, by simp only [Action.opcode]; decide,
    .no_immediate p.inbounds (by simpa [global_simps] using hbyte) p.pos .nop⟩

theorem step_i32_const {data env ctx bt st} (p : Wasm.Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_I32_CONST) :
    StepRecords p visitor observe code.OP_I32_CONST := by
  intro v result final v' h
  rw [dispatch_i32_const] at h
  apply run_step_trace data p.start _ visitor observe hrecords .i32_const ?_ v result final v' h
  intro s a hr
  have hs := code.read_i32_const.spec st data (by have := p.val_capacity; omega)
  rw [hr, WP.spec_ok] at hs
  dsimp only at hs
  exact ⟨.plain (Core.i32Const a), rfl, by simp only [Action.opcode]; decide,
    .of_s32 a p.inbounds (by simpa [global_simps] using hbyte) p.pos hs.2.1⟩

theorem step_i64_const {data env ctx bt st} (p : Wasm.Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_I64_CONST) :
    StepRecords p visitor observe code.OP_I64_CONST := by
  intro v result final v' h
  rw [dispatch_i64_const] at h
  apply run_step_trace data p.start _ visitor observe hrecords .i64_const ?_ v result final v' h
  intro s a hr
  have hs := code.read_i64_const.spec st data (by have := p.val_capacity; omega)
  rw [hr, WP.spec_ok] at hs
  dsimp only at hs
  exact ⟨.plain (ScalarConst.i64 a), rfl, by simp only [Action.opcode]; decide,
    .of_s64 a p.inbounds (by simpa [global_simps] using hbyte) p.pos hs.2.1⟩

theorem step_f32_const {data env ctx bt st} (p : Wasm.Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_F32_CONST) :
    StepRecords p visitor observe code.OP_F32_CONST := by
  intro v result final v' h
  rw [dispatch_f32_const] at h
  apply run_step_trace data p.start _ visitor observe hrecords .f32_const ?_ v result final v' h
  intro s a hr
  have hs := code.read_f32_const.spec st data (by have := p.val_capacity; omega)
  rw [hr, WP.spec_ok] at hs
  dsimp only at hs
  exact ⟨.plain (ScalarConst.f32 a), rfl, by simp only [Action.opcode]; decide,
    .of_f32 a p.inbounds (by simpa [global_simps] using hbyte) p.pos hs.2.1⟩

theorem step_f64_const {data env ctx bt st} (p : Wasm.Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_F64_CONST) :
    StepRecords p visitor observe code.OP_F64_CONST := by
  intro v result final v' h
  rw [dispatch_f64_const] at h
  apply run_step_trace data p.start _ visitor observe hrecords .f64_const ?_ v result final v' h
  intro s a hr
  have hs := code.read_f64_const.spec st data (by have := p.val_capacity; omega)
  rw [hr, WP.spec_ok] at hs
  dsimp only at hs
  exact ⟨.plain (ScalarConst.f64 a), rfl, by simp only [Action.opcode]; decide,
    .of_f64 a p.inbounds (by simpa [global_simps] using hbyte) p.pos hs.2.1⟩

theorem step_drop {data env ctx bt st} (p : Wasm.Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_DROP) :
    StepRecords p visitor observe code.OP_DROP := by
  intro v result final v' h
  rw [dispatch_drop] at h
  apply run_step_trace data p.start _ visitor observe hrecords .drop ?_ v result final v' h
  intro s a hr
  obtain ⟨_, outer, _, _, base, _, ctrls, vals⟩ := p.opened
  have hs := code.pop_stack_type.segment st outer p.current.vals vals
    (by simp [Control.base, ctrls, base])
  change code.pop_stack_type st = .ok (.Ok a, s) at hr
  rw [hr, WP.spec_ok] at hs
  dsimp only at hs
  exact ⟨.plain .DROP, rfl, by simp only [Action.opcode]; decide,
    .no_immediate p.inbounds (by simpa [global_simps] using hbyte)
      (by simpa [hs.2.1] using p.pos) .drop⟩

theorem step_select {data env ctx bt st} (p : Wasm.Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_SELECT) :
    StepRecords p visitor observe code.OP_SELECT := by
  intro v result final v' h
  rw [dispatch_select] at h
  apply run_step_trace data p.start _ visitor observe hrecords .select ?_ v result final v' h
  intro s a hr
  obtain ⟨_, outer, _, _, base, _, ctrls, vals⟩ := p.opened
  have hs := code.read_select.segment st outer p.current.vals vals
    (by simp [Control.base, ctrls, base]) (by have := p.val_capacity; omega)
  rw [hr, WP.spec_ok] at hs
  dsimp only at hs
  exact ⟨.plain (.SELECT none), rfl, by simp only [Action.opcode]; decide,
    .no_immediate p.inbounds (by simpa [global_simps] using hbyte)
      (by simpa [hs.2.1] using p.pos) .select⟩

theorem step_unreachable {data env ctx bt st} (p : Wasm.Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_UNREACHABLE) :
    StepRecords p visitor observe code.OP_UNREACHABLE := by
  intro v result final v' h
  rw [dispatch_unreachable] at h
  apply run_step_trace data p.start _ visitor observe hrecords (fun _ => .unreachable) ?_
    v result final v' h
  intro s a hr
  obtain ⟨_, outer, _, _, base, _, ctrls, vals⟩ := p.opened
  obtain ⟨s', hm, _, _, _, hp⟩ := WP.spec_imp_exists
    (code.mark_unreachable.spec st (p.parents.map WasmFrames.Saved.ctrl) p.current.ctrl ctrls
      (by simp [vals, base]))
  have heq : s' = s := by simpa [code.read_unreachable, hm] using hr
  subst s
  exact ⟨.plain .UNREACHABLE, rfl, by simp only [Action.opcode]; decide,
    .no_immediate p.inbounds (by simpa [global_simps] using hbyte)
      (by simpa [hp] using p.pos) .unreachable⟩

theorem step_local_get {data env ctx bt st} (p : Wasm.Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_LOCAL_GET) :
    StepRecords p visitor observe code.OP_LOCAL_GET := by
  intro v result final v' h
  rw [dispatch_local_get] at h
  apply run_step_trace data p.start _ visitor observe hrecords .local_get ?_ v result final v' h
  intro s a hr
  obtain ⟨C, outer, spine, _, base, typed, ctrls, vals⟩ := p.opened
  have hpoly : Control.polymorphic st = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ctx
      (WasmFrames.enter C p.current.form p.current.ctrl.block_type) := spine.matches.enter _
  have hs := code.read_local_get.prefix st data env ctx outer p.current.vals vals
    (by have := p.val_capacity; omega)
    _ hC p.current.ops (by simpa [hpoly] using typed)
  rw [hr, WP.spec_ok] at hs
  obtain ⟨bytes, suffix, length, bound, encoding⟩ := (hs a rfl).1
  exact ⟨.plain (.LOCAL_GET (.mk_uN a.val)), rfl, by simp only [Action.opcode]; decide,
    .of_immediate p.inbounds (by simpa [global_simps] using hbyte) p.pos
      (.localGet a encoding) ⟨suffix, length, bound⟩⟩

theorem step_local_set {data env ctx bt st} (p : Wasm.Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_LOCAL_SET) :
    StepRecords p visitor observe code.OP_LOCAL_SET := by
  intro v result final v' h
  rw [dispatch_local_set] at h
  apply run_step_trace data p.start _ visitor observe hrecords .local_set ?_ v result final v' h
  intro s a hr
  obtain ⟨C, outer, spine, _, base, typed, ctrls, vals⟩ := p.opened
  have hpoly : Control.polymorphic st = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ctx
      (WasmFrames.enter C p.current.form p.current.ctrl.block_type) := spine.matches.enter _
  have hs := code.read_local_set.prefix st data env ctx outer p.current.vals vals
    (by simp [Control.base, ctrls, base])
    _ hC p.current.ops (by simpa [hpoly] using typed)
  rw [hr, WP.spec_ok] at hs
  obtain ⟨bytes, suffix, length, bound, encoding⟩ := (hs a rfl).1
  exact ⟨.plain (.LOCAL_SET (.mk_uN a.val)), rfl, by simp only [Action.opcode]; decide,
    .of_immediate p.inbounds (by simpa [global_simps] using hbyte) p.pos
      (.localSet a encoding) ⟨suffix, length, bound⟩⟩

theorem step_local_tee {data env ctx bt st} (p : Wasm.Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_LOCAL_TEE) :
    StepRecords p visitor observe code.OP_LOCAL_TEE := by
  intro v result final v' h
  rw [dispatch_local_tee] at h
  apply run_step_trace data p.start _ visitor observe hrecords .local_tee ?_ v result final v' h
  intro s a hr
  obtain ⟨C, outer, spine, _, base, typed, ctrls, vals⟩ := p.opened
  have hpoly : Control.polymorphic st = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ctx
      (WasmFrames.enter C p.current.form p.current.ctrl.block_type) := spine.matches.enter _
  have hs := code.read_local_tee.prefix st data env ctx outer p.current.vals vals
    (by simp [Control.base, ctrls, base])
    (by have := p.val_capacity; omega)
    _ hC p.current.ops (by simpa [hpoly] using typed)
  rw [hr, WP.spec_ok] at hs
  obtain ⟨bytes, suffix, length, bound, encoding⟩ := (hs a rfl).1
  exact ⟨.plain (.LOCAL_TEE (.mk_uN a.val)), rfl, by simp only [Action.opcode]; decide,
    .of_immediate p.inbounds (by simpa [global_simps] using hbyte) p.pos
      (.localTee a encoding) ⟨suffix, length, bound⟩⟩

theorem step_global_get {data env ctx bt st} (p : Wasm.Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_GLOBAL_GET) :
    StepRecords p visitor observe code.OP_GLOBAL_GET := by
  intro v result final v' h
  rw [dispatch_global_get] at h
  apply run_step_trace data p.start _ visitor observe hrecords .global_get ?_ v result final v' h
  intro s a hr
  obtain ⟨C, outer, spine, _, base, typed, ctrls, vals⟩ := p.opened
  have hpoly : Control.polymorphic st = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ctx
      (WasmFrames.enter C p.current.form p.current.ctrl.block_type) := spine.matches.enter _
  have hs := code.read_global_get.prefix st data env ctx outer p.current.vals vals
    (by have := p.val_capacity; omega)
    _ hC p.current.ops (by simpa [hpoly] using typed)
  rw [hr, WP.spec_ok] at hs
  obtain ⟨bytes, suffix, length, bound, encoding⟩ := (hs a rfl).1
  exact ⟨.plain (.GLOBAL_GET (.mk_uN a.val)), rfl, by simp only [Action.opcode]; decide,
    .of_immediate p.inbounds (by simpa [global_simps] using hbyte) p.pos
      (.globalGet a encoding) ⟨suffix, length, bound⟩⟩

theorem step_global_set {data env ctx bt st} (p : Wasm.Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_GLOBAL_SET) :
    StepRecords p visitor observe code.OP_GLOBAL_SET := by
  intro v result final v' h
  rw [dispatch_global_set] at h
  apply run_step_trace data p.start _ visitor observe hrecords .global_set ?_ v result final v' h
  intro s a hr
  obtain ⟨C, outer, spine, _, base, typed, ctrls, vals⟩ := p.opened
  have hpoly : Control.polymorphic st = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ctx
      (WasmFrames.enter C p.current.form p.current.ctrl.block_type) := spine.matches.enter _
  have hs := code.read_global_set.prefix st data env ctx outer p.current.vals vals
    (by simp [Control.base, ctrls, base])
    _ hC p.current.ops (by simpa [hpoly] using typed)
  rw [hr, WP.spec_ok] at hs
  obtain ⟨bytes, suffix, length, bound, encoding⟩ := (hs a rfl).1
  exact ⟨.plain (.GLOBAL_SET (.mk_uN a.val)), rfl, by simp only [Action.opcode]; decide,
    .of_immediate p.inbounds (by simpa [global_simps] using hbyte) p.pos
      (.globalSet a encoding) ⟨suffix, length, bound⟩⟩

theorem step_call {data env ctx bt st} (p : Wasm.Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_CALL) :
    StepRecords p visitor observe code.OP_CALL := by
  intro v result final v' h
  rw [dispatch_call] at h
  apply run_step_trace data p.start _ visitor observe hrecords .call ?_ v result final v' h
  intro s a hr
  obtain ⟨C, outer, spine, _, base, typed, ctrls, vals⟩ := p.opened
  have hpoly : Control.polymorphic st = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ctx
      (WasmFrames.enter C p.current.form p.current.ctrl.block_type) := spine.matches.enter _
  have hs := code.read_call.prefix st data env ctx outer p.current.vals vals
    (by simp [Control.base, ctrls, base])
    (by have := p.val_capacity; omega)
    _ hC p.current.ops (by simpa [hpoly] using typed)
  rw [hr, WP.spec_ok] at hs
  obtain ⟨bytes, suffix, length, bound, encoding⟩ := (hs a rfl).1
  exact ⟨.plain (.CALL (.mk_uN a.val)), rfl, by simp only [Action.opcode]; decide,
    .of_immediate p.inbounds (by simpa [global_simps] using hbyte) p.pos
      (.call a encoding) ⟨suffix, length, bound⟩⟩

theorem step_call_indirect {data env ctx bt st} (p : Wasm.Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_CALL_INDIRECT) :
    StepRecords p visitor observe code.OP_CALL_INDIRECT := by
  intro v result final v' h
  rw [dispatch_call_indirect] at h
  apply run_step_trace data p.start _ visitor observe hrecords .call_indirect ?_ v result final v' h
  intro s a hr
  obtain ⟨C, outer, spine, _, base, typed, ctrls, vals⟩ := p.opened
  have hpoly : Control.polymorphic st = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ctx
      (WasmFrames.enter C p.current.form p.current.ctrl.block_type) := spine.matches.enter _
  have hs := code.read_call_indirect.prefix st data env ctx outer p.current.vals vals
    (by simp [Control.base, ctrls, base]) (by have := p.val_capacity; omega)
    _ hC p.current.ops (by simpa [hpoly] using typed)
  rw [hr, WP.spec_ok] at hs
  obtain ⟨middle, hd, hm, hz, hn⟩ := (hs a rfl).1
  exact ⟨.plain (.CALL_INDIRECT (.mk_uN 0) (.mk_uN a.val)), rfl,
    by simp only [Action.opcode]; decide,
    .of_index_zero a p.inbounds (by simpa [global_simps] using hbyte) p.pos hd hm hz hn⟩

theorem step_memory_size {data env ctx bt st} (p : Wasm.Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_MEMORY_SIZE) :
    StepRecords p visitor observe code.OP_MEMORY_SIZE := by
  intro v result final v' h
  rw [dispatch_memory_size] at h
  apply run_step_trace data p.start _ visitor observe hrecords (fun _ => .memory_size) ?_ v result final v' h
  intro s a hr
  cases a
  obtain ⟨C, outer, spine, _, base, typed, ctrls, vals⟩ := p.opened
  have hpoly : Control.polymorphic st = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ctx
      (WasmFrames.enter C p.current.form p.current.ctrl.block_type) := spine.matches.enter _
  have hs := code.read_memory_size.prefix st data env ctx outer p.current.vals vals
    (by have := p.val_capacity; omega)
    _ hC p.current.ops (by simpa [hpoly] using typed)
  rw [hr, WP.spec_ok] at hs
  obtain ⟨hb, hv, hn⟩ := (hs rfl).1
  exact ⟨.plain .MEMORY_SIZE, rfl, by simp only [Action.opcode]; decide,
    .of_byte 0#u8 p.inbounds (by simpa [global_simps] using hbyte) p.pos .memorySize hb hv hn⟩

theorem step_memory_grow {data env ctx bt st} (p : Wasm.Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_MEMORY_GROW) :
    StepRecords p visitor observe code.OP_MEMORY_GROW := by
  intro v result final v' h
  rw [dispatch_memory_grow] at h
  apply run_step_trace data p.start _ visitor observe hrecords (fun _ => .memory_grow) ?_ v result final v' h
  intro s a hr
  cases a
  obtain ⟨C, outer, spine, _, base, typed, ctrls, vals⟩ := p.opened
  have hpoly : Control.polymorphic st = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ctx
      (WasmFrames.enter C p.current.form p.current.ctrl.block_type) := spine.matches.enter _
  have hs := code.read_memory_grow.prefix st data env ctx outer p.current.vals vals
    (by simp [Control.base, ctrls, base])
    (by have := p.val_capacity; omega)
    _ hC p.current.ops (by simpa [hpoly] using typed)
  rw [hr, WP.spec_ok] at hs
  obtain ⟨hb, hv, hn⟩ := (hs rfl).1
  exact ⟨.plain .MEMORY_GROW, rfl, by simp only [Action.opcode]; decide,
    .of_byte 0#u8 p.inbounds (by simpa [global_simps] using hbyte) p.pos .memoryGrow hb hv hn⟩

theorem step_numeric {data env ctx bt st} (p : Wasm.Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe) (opcode : U8) (operation : Numeric.Operation)
    (hbyte : data.val[p.start.val]'p.inbounds = opcode)
    (hrow : Numeric.opcodeMeaning opcode = some operation) :
    StepRecords p visitor observe opcode := by
  obtain ⟨hook, hh, hcode, hmeaning⟩ := NumericHook.of_meaning hrow
  intro v result final v' h
  rw [dispatch_numeric visitor st data env ctx v opcode operation hook hrow hh] at h
  apply run_step_trace data p.start _ visitor observe hrecords (fun _ => .numeric hook) ?_
    v result final v' h
  intro s a hr
  obtain ⟨_, outer, _, _, base, _, ctrls, vals⟩ := p.opened
  have hs := Numeric.read.segment operation st outer p.current.vals vals
    (by simp [Control.base, ctrls, base]) (by have := p.val_capacity; omega)
  rw [hr, WP.spec_ok] at hs
  dsimp only at hs
  refine ⟨.plain operation.instruction, by simp only [Action.token, hmeaning], ?_,
    .no_immediate p.inbounds hbyte (by simpa [hs.2.1] using p.pos) (.numeric opcode operation hrow)⟩
  change some hook.opcode ≠ some 0x0E#u8
  intro he
  have hv : opcode.val = 14 := by rw [← hcode, Option.some.inj he]; rfl
  have hb := Numeric.NumericOp.bounds hrow
  omega

theorem step_memory {data env ctx bt st} (p : Wasm.Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe) (opcode : U8) (operation : MemoryMeaning.Operation)
    (hbyte : data.val[p.start.val]'p.inbounds = opcode)
    (hrow : MemoryMeaning.opcodeMeaning opcode = some operation) :
    StepRecords p visitor observe opcode := by
  obtain ⟨hook, hh, _, hmeaning⟩ := MemoryHook.of_meaning hrow
  intro v result final v' h
  rw [dispatch_memory visitor st data env ctx v opcode operation hook hrow hh] at h
  apply run_step_trace data p.start _ visitor observe hrecords (.memory hook) ?_
    v result final v' h
  intro s arg hr
  obtain ⟨C, outer, spine, _, base, typed, ctrls, vals⟩ := p.opened
  have hpoly : Control.polymorphic st = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ctx
      (WasmFrames.enter C p.current.form p.current.ctrl.block_type) := spine.matches.enter _
  have hs :
      (if operation.store then code.read_store st data env operation.ty operation.naturalAlign
        else code.read_load st data env operation.ty operation.naturalAlign) ⦃
        EnvOps.MemoryPost data st outer p.current.vals
          (WasmFrames.enter C p.current.form p.current.ctrl.block_type) p.current.ops operation.op ⦄ := by
    cases hstore : operation.store with
    | false =>
      simpa only [hstore, Bool.false_eq_true, ↓reduceIte] using
        code.read_load.prefix st data env ctx outer p.current.vals vals
          (by simp [Control.base, ctrls, base]) (by have := p.val_capacity; omega)
          _ hC p.current.ops (by simpa [hpoly] using typed) opcode operation hrow hstore
    | true =>
      simpa only [hstore, ↓reduceIte] using
        code.read_store.prefix st data env ctx outer p.current.vals vals
          (by simp [Control.base, ctrls, base])
          _ hC p.current.ops (by simpa [hpoly] using typed) opcode operation hrow hstore
  rw [hr, WP.spec_ok] at hs
  obtain ⟨middle, ha, ho⟩ := (hs arg rfl).1
  exact ⟨.plain (operation.op arg), by simp only [Action.token, hmeaning],
    by cases hook <;> simp only [Action.opcode, MemoryHook.opcode] <;> decide,
    .of_memory operation arg hrow p.inbounds hbyte p.pos ha ho⟩

end Itasca.VisitorTrace
