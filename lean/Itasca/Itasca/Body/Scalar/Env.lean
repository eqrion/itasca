import Itasca.Body.Control.Frame
import Itasca.Handler.ScalarCompleteness
import Itasca.Handler.ScalarOperations
import Itasca.Body.Step.ScalarContext
import Itasca.Visitor.RunTrace
import Itasca.Body.EmptyVisitorLoop

open WebAssembly

/-!
# Env

Environment-dependent scalar readers return normally and retain their decoded prefix. The resulting contracts connect concrete lookups to source environment typing.
-/

/-! ## ReadersTotal -/

section

/-!
# Totality of the scalar readers

Totality of the extracted `code.take_*` and `code.read_*` helpers used by the shared scalar
`code.step` arms (locals, globals, memory, constants, `drop` and `select`). Each lemma in
`Body.ScalarReaders` shows that the reader terminates, preserves `Body.Control.Shape` and never moves
the cursor back, on arbitrary bytes and environments.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- Pushing a value preserves frame bounds for arbitrary frames. -/
theorem code.push_val.shape_total (st : code.OpIterState) (t : code.StackType)
    (hs : Body.Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.push_val st t ⦃ s => Body.Control.Shape s ∧ s.ctrls = st.ctrls ∧ s.pos = st.pos ∧
      s.vals.val.length = st.vals.val.length + 1 ⦄ := by
  apply WP.spec_mono (code.push_val.spec st t hsize)
  rintro s ⟨hv, hc, hp⟩
  exact ⟨hs.replace_operands hc (by simp [hv]; have := hs.base_le; omega),
    hc, hp, by simp [hv]⟩

namespace Body.ScalarReaders

private theorem same_stacks {st s : code.OpIterState} (hs : Body.Control.Shape st)
    (hc : s.ctrls = st.ctrls) (hv : s.vals = st.vals) : Body.Control.Shape s :=
  ⟨by simpa [hc] using hs.ordered, by simpa [hc, hv] using hs.bounded⟩

theorem take_local (st : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (hs : Body.Control.Shape st) :
    code.take_local st data ctx ⦃ r => Body.Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ∧ r.2.vals.val.length = st.vals.val.length ⦄ := by
  apply WP.spec_mono (code.take_local.spec st data ctx)
  rintro ⟨r, s⟩ ⟨hv, hc, hp⟩
  dsimp only at hv hc hp ⊢
  refine ⟨same_stacks hs hc hv, hc, ?_, by simp [hv]⟩
  cases r with
  | Ok pair => exact (Binary.Leb128.Decoded.span _ _ _ _ hp.1).1.le
  | Err e =>
    rcases hp with ⟨_, hp⟩ | ⟨_, idx, hd, _⟩
    · simp [hp]
    · exact (Binary.Leb128.Decoded.span _ _ _ _ hd).1.le

theorem take_global (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (hs : Body.Control.Shape st) :
    code.take_global st data env ⦃ r => Body.Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ∧ r.2.vals.val.length = st.vals.val.length ⦄ := by
  apply WP.spec_mono (code.take_global.spec st data env)
  rintro ⟨r, s⟩ ⟨hv, hc, hp⟩
  dsimp only at hv hc hp ⊢
  refine ⟨same_stacks hs hc hv, hc, ?_, by simp [hv]⟩
  cases r with
  | Ok pair => exact (Binary.Leb128.Decoded.span _ _ _ _ hp.1).1.le
  | Err e =>
    rcases hp with ⟨_, hp⟩ | ⟨_, idx, hd, _⟩
    · simp [hp]
    · exact (Binary.Leb128.Decoded.span _ _ _ _ hd).1.le

theorem reserved_zero (st : code.OpIterState) (data : Slice U8)
    (hs : Body.Control.Shape st) :
    code.read_reserved_zero st data ⦃ r => Body.Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ∧ r.2.vals.val.length = st.vals.val.length ⦄ := by
  apply WP.spec_mono (code.read_reserved_zero.spec st data)
  rintro ⟨r, s⟩ ⟨hv, hc, hp⟩
  dsimp only at hv hc hp ⊢
  refine ⟨same_stacks hs hc hv, hc, ?_, by simp [hv]⟩
  cases r with
  | Ok u => obtain ⟨_, _, hp⟩ := hp; omega
  | Err e => simp [hp.1]

theorem memarg (st : code.OpIterState) (data : Slice U8)
    (hs : Body.Control.Shape st) :
    code.read_memarg st data ⦃ r => Body.Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ∧ r.2.vals.val.length = st.vals.val.length ⦄ := by
  apply WP.spec_mono (code.read_memarg.spec st data)
  rintro ⟨r, s⟩ ⟨hv, hc, hp⟩
  dsimp only at hv hc hp ⊢
  refine ⟨same_stacks hs hc hv, hc, ?_, by simp [hv]⟩
  cases r with
  | Ok arg =>
    obtain ⟨middle, h1, h2⟩ := hp
    exact le_trans (Binary.Leb128.Decoded.span _ _ _ _ h1).1.le
      (Binary.Leb128.Decoded.span _ _ _ _ h2).1.le
  | Err e => simp [hp.1]

attribute [local step] take_local take_global reserved_zero memarg
  code.pop_with_type.total code.pop_stack_type.total code.push_val.shape_total
  code.require_memory.spec code.check_memory_and_alignment.spec code.join_stack_type.spec

theorem local_get (st : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (hs : Body.Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_local_get st data ctx ⦃ r => Body.Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ⦄ := by
  unfold code.read_local_get
  step*
  cases val
  step*

theorem local_set (st : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (hs : Body.Control.Shape st) (_hsize : st.vals.val.length < Usize.max) :
    code.read_local_set st data ctx ⦃ r => Body.Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ⦄ := by
  unfold code.read_local_set
  step*
  cases val
  step*

theorem local_tee (st : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (hs : Body.Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_local_tee st data ctx ⦃ r => Body.Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ⦄ := by
  unfold code.read_local_tee
  step*
  cases val
  step*

theorem global_get (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (hs : Body.Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_global_get st data env ⦃ r => Body.Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ⦄ := by
  unfold code.read_global_get
  step*
  cases val
  step*

theorem global_set (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (hs : Body.Control.Shape st) (_hsize : st.vals.val.length < Usize.max) :
    code.read_global_set st data env ⦃ r => Body.Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ⦄ := by
  unfold code.read_global_set
  step*
  cases val
  step*

theorem memory_size (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (hs : Body.Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_memory_size st data env ⦃ r => Body.Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ⦄ := by
  unfold code.read_memory_size
  step*

theorem memory_grow (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (hs : Body.Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_memory_grow st data env ⦃ r => Body.Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ⦄ := by
  unfold code.read_memory_grow
  step*

theorem load (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ty : wasm_types.ValueType) (align : U32)
    (hs : Body.Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_load st data env ty align ⦃ r => Body.Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ⦄ := by
  unfold code.read_load
  step*

theorem store (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ty : wasm_types.ValueType) (align : U32)
    (hs : Body.Control.Shape st) (_hsize : st.vals.val.length < Usize.max) :
    code.read_store st data env ty align ⦃ r => Body.Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ⦄ := by
  unfold code.read_store
  step*

@[local step] private theorem select_type_total (t : code.StackType) :
    code.is_select_type t ⦃ _ => True ⦄ := by simp

theorem select (st : code.OpIterState)
    (hs : Body.Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_select st ⦃ r => Body.Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ⦄ := by
  unfold code.read_select
  step*

theorem drop (st : code.OpIterState)
    (hs : Body.Control.Shape st) (_hsize : st.vals.val.length < Usize.max) :
    code.read_drop st ⦃ r => Body.Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ⦄ := by
  unfold code.read_drop
  step*

theorem i32_const (st : code.OpIterState) (data : Slice U8)
    (hs : Body.Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_i32_const st data ⦃ r => Body.Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ⦄ := by
  apply WP.spec_mono (code.read_i32_const.spec st data hsize)
  rintro ⟨r, s⟩ ⟨hc, hp⟩
  dsimp only at hc hp ⊢
  cases r with
  | Err e => simpa [hp.2] using (show Body.Control.Shape st ∧ st.ctrls = st.ctrls ∧ st.pos.val ≤ st.pos.val from ⟨hs, rfl, le_refl _⟩)
  | Ok value =>
    obtain ⟨hd, hv⟩ := hp
    refine ⟨hs.replace_operands hc ?_, hc, (Binary.SignedLeb32.Decoded.span _ _ _ _ hd).1.le⟩
    simp only [hv, List.length_append, List.length_singleton]
    have := hs.base_le
    omega

theorem i64_const (st : code.OpIterState) (data : Slice U8)
    (hs : Body.Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_i64_const st data ⦃ r => Body.Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ⦄ := by
  apply WP.spec_mono (code.read_i64_const.spec st data hsize)
  rintro ⟨r, s⟩ ⟨hc, hp⟩
  dsimp only at hc hp ⊢
  cases r with
  | Err e => simpa [hp.2] using (show Body.Control.Shape st ∧ st.ctrls = st.ctrls ∧ st.pos.val ≤ st.pos.val from ⟨hs, rfl, le_refl _⟩)
  | Ok value =>
    obtain ⟨hd, hv⟩ := hp
    refine ⟨hs.replace_operands hc ?_, hc, (Binary.SignedLeb64.Decoded.span _ _ _ _ hd).1.le⟩
    simp only [hv, List.length_append, List.length_singleton]
    have := hs.base_le
    omega

theorem f32_const (st : code.OpIterState) (data : Slice U8)
    (hs : Body.Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_f32_const st data ⦃ r => Body.Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ⦄ := by
  apply WP.spec_mono (code.read_f32_const.spec st data hsize)
  rintro ⟨r, s⟩ ⟨hc, hp⟩
  dsimp only at hc hp ⊢
  cases r with
  | Err e => simpa [hp.2] using (show Body.Control.Shape st ∧ st.ctrls = st.ctrls ∧ st.pos.val ≤ st.pos.val from ⟨hs, rfl, le_refl _⟩)
  | Ok value =>
    obtain ⟨hd, hv⟩ := hp
    refine ⟨hs.replace_operands hc ?_, hc, by have := (Binary.FloatBits.Decoded.span _ _ _ _ _ hd).1; omega⟩
    simp only [hv, List.length_append, List.length_singleton]
    have := hs.base_le
    omega

theorem f64_const (st : code.OpIterState) (data : Slice U8)
    (hs : Body.Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_f64_const st data ⦃ r => Body.Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ⦄ := by
  apply WP.spec_mono (code.read_f64_const.spec st data hsize)
  rintro ⟨r, s⟩ ⟨hc, hp⟩
  dsimp only at hc hp ⊢
  cases r with
  | Err e => simpa [hp.2] using (show Body.Control.Shape st ∧ st.ctrls = st.ctrls ∧ st.pos.val ≤ st.pos.val from ⟨hs, rfl, le_refl _⟩)
  | Ok value =>
    obtain ⟨hd, hv⟩ := hp
    refine ⟨hs.replace_operands hc ?_, hc, by have := (Binary.FloatBits.Decoded.span _ _ _ _ _ hd).1; omega⟩
    simp only [hv, List.length_append, List.length_singleton]
    have := hs.base_le
    omega

end Body.ScalarReaders
end Itasca

end

/-! ## Total -/

section

/-!
# Scalar totality

Totality of the shared `code.step` arms for non-control opcodes. `scalar_total` shows that the
dispatcher terminates on structurally bounded stacks, preserves control depth and never moves the
cursor back, for any visitor whose callbacks return. `memory_meaning_exists` shows that every
memory opcode has a meaning.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body

private theorem run_total {A V : Type}
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (hook : V → code.OpIterState → A → Result (core.result.Result Unit error.VisitError × V))
    (v : V) (Q : code.OpIterState → Prop)
    (hr : read ⦃ r => Q r.2 ⦄)
    (hh : ∀ s a, ∃ res v', hook v s a = .ok (res, v')) :
    Visitor.Core.run read hook v ⦃ r => Q r.2.1 ⦄ := by
  have hr' : read ⦃ r => Q r.2 ∧ ∀ a, r.1 = .Ok a → True ⦄ := by
    apply WP.spec_mono hr
    intro r h
    exact ⟨h, by simp⟩
  apply WP.spec_mono (Visitor.Core.run.spec read hook v Q (fun _ _ => True) hr' hh)
  intro r h
  exact h.1

private theorem run_scalar {A V : Type} (st : code.OpIterState)
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (hook : V → code.OpIterState → A → Result (core.result.Result Unit error.VisitError × V))
    (v : V)
    (hr : read ⦃ r => Body.Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧ st.pos.val ≤ r.2.pos.val ⦄)
    (hh : ∀ s a, ∃ res v', hook v s a = .ok (res, v')) :
    Visitor.Core.run read hook v ⦃ r => Body.Control.Shape r.2.1 ∧
      r.2.1.ctrls.val.length = st.ctrls.val.length ∧ st.pos.val ≤ r.2.1.pos.val ⦄ := by
  apply run_total read hook v (fun s => Body.Control.Shape s ∧
    s.ctrls.val.length = st.ctrls.val.length ∧ st.pos.val ≤ s.pos.val)
  · apply WP.spec_mono hr
    rintro r ⟨hs, hc, hp⟩
    exact ⟨hs, by simp [hc], hp⟩
  · exact hh

/-- Every opcode in the load and store range `0x28` to `0x3e` has a memory meaning. -/
theorem memory_meaning_exists (opcode : U8)
    (hlo : 0x28 ≤ opcode.val) (hhi : opcode.val ≤ 0x3E) :
    ∃ operation, Body.MemoryMeaning.opcodeMeaning opcode = some operation := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  change 40 ≤ n at hlo
  change n ≤ 62 at hhi
  interval_cases n <;> exact ⟨_, rfl⟩

/-- The shared scalar dispatcher is total for arbitrary structurally bounded
frames. It preserves control depth and never moves the cursor back. -/
theorem scalar_total {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (opcode : U8) (v : V) (hs : Body.Control.Shape st)
    (hsize : st.vals.val.length < Usize.max)
    (hscalar : opcode.val ∉ controlOpcodes) (hvisitor : Visitor.Total visitor) :
    code.step visitor st data env ctx opcode v ⦃ r => Body.Control.Shape r.2.1 ∧
      r.2.1.ctrls.val.length = st.ctrls.val.length ∧ st.pos.val ≤ r.2.1.pos.val ⦄ := by
  by_cases hhigh : 0x45 ≤ opcode.val
  · rw [code.step.numeric_dispatch visitor st data env ctx opcode v hhigh]
    apply WP.spec_mono (code.step_numeric.total visitor st opcode v hs hsize hvisitor)
    rintro r ⟨hs', hc, hp, _⟩
    exact ⟨hs', by simp [hc], by simp [hp]⟩
  by_cases hmemory : 0x28 ≤ opcode.val ∧ opcode.val ≤ 0x3E
  · obtain ⟨operation, hm⟩ := memory_meaning_exists opcode hmemory.1 hmemory.2
    rw [code.step_memory.dispatch visitor st data env ctx v opcode operation hm]
    apply run_scalar st
    · split
      · exact ScalarReaders.store st data env operation.ty operation.naturalAlign hs hsize
      · exact ScalarReaders.load st data env operation.ty operation.naturalAlign hs hsize
    · exact fun s _ => hvisitor.visit_memory v s opcode _
  by_cases h_nop : opcode = code.OP_NOP
  · subst opcode
    apply WP.spec_mono (code.step_nop.total visitor st data env ctx v hvisitor.to_core)
    intro r hr
    simp [hr, hs]
  by_cases h_unreachable : opcode = code.OP_UNREACHABLE
  · subst opcode
    rw [Visitor.Dispatch.dispatch_unreachable]
    apply run_total _ _ v (fun s => Body.Control.Shape s ∧
      s.ctrls.val.length = st.ctrls.val.length ∧ st.pos.val ≤ s.pos.val)
    · unfold code.read_unreachable
      step*
    · exact fun s _ => hvisitor.on_unreachable v s
  by_cases h_i32_const : opcode = code.OP_I32_CONST
  · subst opcode
    rw [Visitor.Dispatch.dispatch_i32_const]
    exact run_scalar st _ _ v (ScalarReaders.i32_const st data hs hsize)
      (fun s a => hvisitor.on_i32_const v s a)
  by_cases h_i64_const : opcode = code.OP_I64_CONST
  · subst opcode
    rw [Visitor.Dispatch.dispatch_i64_const]
    exact run_scalar st _ _ v (ScalarReaders.i64_const st data hs hsize)
      (fun s a => hvisitor.on_i64_const v s a)
  by_cases h_f32_const : opcode = code.OP_F32_CONST
  · subst opcode
    rw [Visitor.Dispatch.dispatch_f32_const]
    exact run_scalar st _ _ v (ScalarReaders.f32_const st data hs hsize)
      (fun s a => hvisitor.on_f32_const v s a)
  by_cases h_f64_const : opcode = code.OP_F64_CONST
  · subst opcode
    rw [Visitor.Dispatch.dispatch_f64_const]
    exact run_scalar st _ _ v (ScalarReaders.f64_const st data hs hsize)
      (fun s a => hvisitor.on_f64_const v s a)
  by_cases h_drop : opcode = code.OP_DROP
  · subst opcode
    rw [Visitor.Dispatch.dispatch_drop]
    exact run_scalar st _ _ v (ScalarReaders.drop st hs hsize)
      (fun s a => hvisitor.on_drop v s a)
  by_cases h_select : opcode = code.OP_SELECT
  · subst opcode
    rw [code.step_select.dispatch]
    exact run_scalar st _ _ v (ScalarReaders.select st hs hsize)
      (fun s a => hvisitor.on_select v s a)
  by_cases h_local_get : opcode = code.OP_LOCAL_GET
  · subst opcode
    rw [code.step_local_get.dispatch]
    exact run_scalar st _ _ v (ScalarReaders.local_get st data ctx hs hsize)
      (fun s a => hvisitor.on_local_get v s a)
  by_cases h_local_set : opcode = code.OP_LOCAL_SET
  · subst opcode
    rw [code.step_local_set.dispatch]
    exact run_scalar st _ _ v (ScalarReaders.local_set st data ctx hs hsize)
      (fun s a => hvisitor.on_local_set v s a)
  by_cases h_local_tee : opcode = code.OP_LOCAL_TEE
  · subst opcode
    rw [code.step_local_tee.dispatch]
    exact run_scalar st _ _ v (ScalarReaders.local_tee st data ctx hs hsize)
      (fun s a => hvisitor.on_local_tee v s a)
  by_cases h_global_get : opcode = code.OP_GLOBAL_GET
  · subst opcode
    rw [code.step_global_get.dispatch]
    exact run_scalar st _ _ v (ScalarReaders.global_get st data env hs hsize)
      (fun s a => hvisitor.on_global_get v s a)
  by_cases h_global_set : opcode = code.OP_GLOBAL_SET
  · subst opcode
    rw [code.step_global_set.dispatch]
    exact run_scalar st _ _ v (ScalarReaders.global_set st data env hs hsize)
      (fun s a => hvisitor.on_global_set v s a)
  by_cases h_memory_size : opcode = code.OP_MEMORY_SIZE
  · subst opcode
    rw [code.step_memory_size.dispatch]
    exact run_scalar st _ _ v (ScalarReaders.memory_size st data env hs hsize)
      (fun s _ => hvisitor.on_memory_size v s)
  by_cases h_memory_grow : opcode = code.OP_MEMORY_GROW
  · subst opcode
    rw [code.step_memory_grow.dispatch]
    exact run_scalar st _ _ v (ScalarReaders.memory_grow st data env hs hsize)
      (fun s _ => hvisitor.on_memory_grow v s)
  have hreserved : (0x06 ≤ opcode.val ∧ opcode.val ≤ 0x0A) ∨
      (0x12 ≤ opcode.val ∧ opcode.val ≤ 0x19) ∨
      (0x1C ≤ opcode.val ∧ opcode.val ≤ 0x1F) ∨
      (0x25 ≤ opcode.val ∧ opcode.val ≤ 0x27) := by
    simp only [controlOpcodes, List.mem_cons, not_or] at hscalar
    simp only [global_simps] at *
    scalar_tac
  rw [code.step.reserved visitor st data env ctx opcode v hreserved]
  simp [hs]

end Itasca.Body

end

/-! ## Prefix -/

section

/-!
# Scalar typed prefixes

Re-proves the typed-prefix effect of the shared scalar handlers against the Wasm 2.0
`TypedPrefix` zipper. `TypedPrefix.nop`, `.unreachable` and the constant lemmas extend a prefix
by one instruction, `NumericEffect.prefix`, `Popped.prefix_drop` and
`SelectEffect.prefix` do so for stack effects. `NumericReader` and
`StackReader` lift these facts to shared reader specifications.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body

open Body.Stack

theorem TypedPrefix.nop {C : context} {inputs : List valtype} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} (h : TypedPrefix C inputs ops poly vals) (hC : wf_context C) :
    TypedPrefix C inputs (ops ++ [.NOP]) poly vals := by
  apply h.append hC .NOP .instr_case_0
  intro ts ht
  refine ⟨ts, ht, ?_⟩
  simpa using Instrs_ok.frame C [.NOP] ts [] []
    (.instr C .NOP [] [] (.nop C hC .instr_case_0) hC .instr_case_0)
    hC (by simp [Forall]; exact .instr_case_0)

theorem TypedPrefix.unreachable {C : context} {inputs : List valtype} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} (h : TypedPrefix C inputs ops poly vals) (hC : wf_context C) :
    TypedPrefix C inputs (ops ++ [.UNREACHABLE]) true [] := by
  apply h.append hC .UNREACHABLE .instr_case_1
  intro ts _
  exact ⟨stackTypes vals, realizes_default poly vals,
    .instr C .UNREACHABLE (stackTypes vals) ts
      (.unreachable C _ ts hC .instr_case_1) hC .instr_case_1⟩

/-- Constants extend a prefix with arbitrary frame parameters. -/
theorem TypedPrefix.i32_const {C : context} {inputs : List valtype} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} (h : TypedPrefix C inputs ops poly vals)
    (hC : wf_context C) (value : I32) :
    TypedPrefix C inputs (ops ++ [Spec.i32Const value]) poly (vals ++ [.Val .I32]) := by
  apply h.append hC _ (Spec.i32_const_wf value)
  intro out hout
  obtain ⟨before, rfl, hb⟩ := Realizes.snoc_val .I32 hout
  exact ⟨before, hb, Spec.i32_const_framed C hC value before⟩

theorem TypedPrefix.i64_const {C : context} {inputs : List valtype} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} (h : TypedPrefix C inputs ops poly vals)
    (hC : wf_context C) (value : I64) :
    TypedPrefix C inputs (ops ++ [Spec.Constants.i64 value]) poly (vals ++ [.Val .I64]) := by
  apply h.append hC _ (Spec.Constants.i64_wf value)
  intro out hout
  obtain ⟨before, rfl, hb⟩ := Realizes.snoc_val .I64 hout
  exact ⟨before, hb, Spec.Constants.i64_framed C hC value before⟩

theorem TypedPrefix.f32_const {C : context} {inputs : List valtype} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} (h : TypedPrefix C inputs ops poly vals)
    (hC : wf_context C) (value : U32) :
    TypedPrefix C inputs (ops ++ [Spec.Constants.f32 value]) poly (vals ++ [.Val .F32]) := by
  apply h.append hC _ (Spec.Constants.f32_wf value)
  intro out hout
  obtain ⟨before, rfl, hb⟩ := Realizes.snoc_val .F32 hout
  exact ⟨before, hb, Spec.Constants.f32_framed C hC value before⟩

theorem TypedPrefix.f64_const {C : context} {inputs : List valtype} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} (h : TypedPrefix C inputs ops poly vals)
    (hC : wf_context C) (value : U64) :
    TypedPrefix C inputs (ops ++ [Spec.Constants.f64 value]) poly (vals ++ [.Val .F64]) := by
  apply h.append hC _ (Spec.Constants.f64_wf value)
  intro out hout
  obtain ⟨before, rfl, hb⟩ := Realizes.snoc_val .F64 hout
  exact ⟨before, hb, Spec.Constants.f64_framed C hC value before⟩

/-- A typed prefix is a resume prefix with no saved arguments. -/
theorem ResumePrefix.of_prefix {C inputs ops poly vals}
    (h : TypedPrefix C inputs ops poly vals) : ResumePrefix C inputs ops poly vals [] :=
  ⟨h.wellFormed, fun ts ht => by simpa using h.typed ts ht⟩

end Itasca.Body

namespace Itasca.Body.Stack.Semantics

theorem NumericEffect.prefix {initial : List valtype} {poly before inputs output after}
    (h : NumericEffect poly before inputs output after)
    (C : context) (hC : wf_context C) (ops : List instr) (op : instr)
    (htyped : Body.TypedPrefix C initial ops poly before) (hwf : wf_instr op)
    (hop : Instr_ok C op (.mk_functype (.mk_list (inputs.map Translation.valueType))
      (.mk_list [Translation.valueType output]))) :
    Body.TypedPrefix C initial (ops ++ [op]) poly after := by
  obtain ⟨rest, rfl, htransfer⟩ := h
  apply htyped.append hC op hwf
  intro out hout
  obtain ⟨front, u, rfl, hfront, hu⟩ := hout.snoc_inv
  change u = Translation.valueType output at hu
  subst u
  refine ⟨front ++ inputs.map Translation.valueType, htransfer front hfront, ?_⟩
  exact .frame C [op] front _ _ (.instr C op _ _ hop hC hwf) hC (by simpa [Forall] using hwf)

theorem Popped.prefix_drop {initial : List valtype} {poly before t after} (h : Popped poly before t after)
    (C : context) (hC : wf_context C) (ops : List instr)
    (htyped : Body.TypedPrefix C initial ops poly before) :
    Body.TypedPrefix C initial (ops ++ [.DROP]) poly after := by
  apply htyped.append hC .DROP .instr_case_2
  intro out hout
  let u := match t with | .Val vt => Translation.valueType vt | .Bot => valtype.I32
  have haccept : Body.Stack.Accepts t u := by cases t <;> simp [Body.Stack.Accepts, u]
  refine ⟨out ++ [u], h.realizes out u haccept hout, ?_⟩
  simpa using Instrs_ok.frame C [.DROP] out [u] []
    (.instr C .DROP [u] [] (.drop C u hC .instr_case_2) hC .instr_case_2)
    hC (by simp [Forall]; exact .instr_case_2)

theorem SelectEffect.prefix {initial : List valtype} {poly before t after} (h : SelectEffect poly before t after)
    (C : context) (hC : wf_context C) (ops : List instr)
    (htyped : Body.TypedPrefix C initial ops poly before) :
    Body.TypedPrefix C initial (ops ++ [.SELECT none]) poly after := by
  obtain ⟨hselect, rest, rfl, htransfer⟩ := h
  apply htyped.append hC (.SELECT none) (.instr_case_3 _)
  intro out hout
  obtain ⟨front, u, rfl, hf, hu⟩ := hout.snoc_inv
  refine ⟨front ++ [selectedType t, selectedType t, .I32], htransfer front hf, ?_⟩
  apply Instrs_ok.frame C [.SELECT none] front _ _ _ hC (by simp [Forall]; exact .instr_case_3 _)
  apply Instrs_ok.sub C [.SELECT none] _ _ _ _
    (.instr C _ _ _ (selected_type_typed C hC t hselect) hC (.instr_case_3 _))
    _ _ hC (by simp [Forall]; exact .instr_case_3 _)
  · exact .mk_Resulttype_sub _ _ rfl (by simp [Forall₂, Valtype_sub.refl])
  · exact .mk_Resulttype_sub _ _ rfl (by simpa [Forall₂] using selected_type_sub hu)

end Itasca.Body.Stack.Semantics

end

/-! ## Env -/

section

/-!
# Local and global readers

Typed-prefix specs of the extracted `code.read_local_get`, `code.read_local_set`,
`code.read_local_tee`, `code.read_global_get` and `code.read_global_set` against the Wasm 2.0
`TypedPrefix` zipper. `Body.Scalar.IndexPost` is their shared postcondition.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.Scalar

/-- Successful indexed instructions expose both byte provenance and the typed
operand segment. The surrounding WP also proves totality on rejection. -/
def IndexPost (inputs : List valtype) (data : Slice U8) (st : code.OpIterState)
    (outer segment : List code.StackType) (C : context) (ops : List instr)
    (op : U32 → instr)
    (r : core.result.Result U32 error.OpError × code.OpIterState) : Prop :=
  ∀ idx, r.1 = .Ok idx →
    Binary.Leb128.Decoded data st.pos idx r.2.pos ∧ r.2.ctrls = st.ctrls ∧
      ∃ rest, r.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length + 1 ∧
        Body.TypedPrefix C inputs (ops ++ [op idx]) (Body.Control.polymorphic st) rest

end Itasca.Body.Scalar

namespace Itasca

theorem code.read_local_get.prefix {inputs : List valtype} (st : code.OpIterState) (data : Slice U8)
    (env : metadata.Env) (ctx : code.Context) (outer segment : List code.StackType)
    (hvals : st.vals.val = outer ++ segment) (hsize : st.vals.val.length < Usize.max)
    (C : context) (hC : Translation.Environment.Matches env ctx C) (ops : List instr)
    (htyped : Body.TypedPrefix C inputs ops (Body.Control.polymorphic st) segment) :
    code.read_local_get st data ctx ⦃ Body.Scalar.IndexPost inputs data st outer segment C ops
      (fun idx => .LOCAL_GET (.mk_uN idx.val)) ⦄ := by
  obtain ⟨⟨r, s⟩, hr, hv, hc, hout⟩ := WP.spec_imp_exists (code.take_local.spec st data ctx)
  dsimp only at hv hc hout
  cases r with
  | Err e =>
      simp [code.read_local_get, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Body.Scalar.IndexPost]
  | Ok pair =>
      obtain ⟨idx, t⟩ := pair
      obtain ⟨hd, hi, ht⟩ := hout
      obtain ⟨s', hp, hv', hc', hpos⟩ := WP.spec_imp_exists
        (code.push_val.spec s (.Val t) (by simpa [hv] using hsize))
      have htyping := (Body.ResumePrefix.of_prefix htyped).finish hC.wf
        (.LOCAL_GET (.mk_uN idx.val)) [t] (.instr_case_43 _ (Translation.Environment.index_wf idx))
        (hC.local_get idx t hi ht)
      rw [WP.spec_equiv_exists]
      refine ⟨(.Ok idx, s'), ?_, ?_⟩
      · simp [code.read_local_get, hr, hp, core.result.Result.Insts.CoreOpsTry.branch]
      · intro ix heq
        cases heq
        exact ⟨by simpa [hpos] using hd, hc'.trans hc, segment ++ [.Val t],
          by simpa [hv, hvals, List.append_assoc] using hv', by simp, by simpa using htyping⟩

theorem code.read_local_set.prefix {inputs : List valtype} (st : code.OpIterState) (data : Slice U8)
    (env : metadata.Env) (ctx : code.Context) (outer segment : List code.StackType)
    (hvals : st.vals.val = outer ++ segment) (hbase : (Body.Control.base st).val = outer.length)
    (C : context) (hC : Translation.Environment.Matches env ctx C) (ops : List instr)
    (htyped : Body.TypedPrefix C inputs ops (Body.Control.polymorphic st) segment) :
    code.read_local_set st data ctx ⦃ Body.Scalar.IndexPost inputs data st outer segment C ops
      (fun idx => .LOCAL_SET (.mk_uN idx.val)) ⦄ := by
  obtain ⟨⟨r, s⟩, hr, hv, hc, hout⟩ := WP.spec_imp_exists (code.take_local.spec st data ctx)
  dsimp only at hv hc hout
  cases r with
  | Err e =>
      simp [code.read_local_set, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Body.Scalar.IndexPost]
  | Ok pair =>
      obtain ⟨idx, t⟩ := pair
      obtain ⟨hd, hi, ht⟩ := hout
      obtain ⟨⟨r', s'⟩, hp, hc', hpos, rest, hv', hlen, hout'⟩ := WP.spec_imp_exists
        (code.pop_with_type.realizes s outer segment t (by simpa [hv] using hvals)
          (by simpa [Body.Control.base, hc] using hbase))
      dsimp only at hc' hpos hv' hlen hout'
      cases r' with
      | Err e =>
          simp [code.read_local_set, hr, hp, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Body.Scalar.IndexPost]
      | Ok popped =>
          have hpop : ∀ ts, Body.Stack.Realizes (Body.Control.polymorphic st) rest ts →
              Body.Stack.Realizes (Body.Control.polymorphic st) segment (ts ++ [Translation.valueType t]) := by
            simpa [Body.Control.polymorphic, hc] using hout'.2
          have htyping := (Body.ResumePrefix.after_pop htyped hpop).finish hC.wf
            (.LOCAL_SET (.mk_uN idx.val)) [] (.instr_case_44 _ (Translation.Environment.index_wf idx))
            (hC.local_set idx t hi ht)
          rw [WP.spec_equiv_exists]
          refine ⟨(.Ok idx, s'), ?_, ?_⟩
          · simp [code.read_local_set, hr, hp, core.result.Result.Insts.CoreOpsTry.branch]
          · intro ix heq
            cases heq
            exact ⟨by simpa [hpos] using hd, hc'.trans hc, rest, hv', by omega,
              by simpa using htyping⟩

theorem code.read_local_tee.prefix {inputs : List valtype} (st : code.OpIterState) (data : Slice U8)
    (env : metadata.Env) (ctx : code.Context) (outer segment : List code.StackType)
    (hvals : st.vals.val = outer ++ segment) (hbase : (Body.Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max)
    (C : context) (hC : Translation.Environment.Matches env ctx C) (ops : List instr)
    (htyped : Body.TypedPrefix C inputs ops (Body.Control.polymorphic st) segment) :
    code.read_local_tee st data ctx ⦃ Body.Scalar.IndexPost inputs data st outer segment C ops
      (fun idx => .LOCAL_TEE (.mk_uN idx.val)) ⦄ := by
  obtain ⟨⟨r, s⟩, hr, hv, hc, hout⟩ := WP.spec_imp_exists (code.take_local.spec st data ctx)
  dsimp only at hv hc hout
  cases r with
  | Err e =>
      simp [code.read_local_tee, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Body.Scalar.IndexPost]
  | Ok pair =>
      obtain ⟨idx, t⟩ := pair
      obtain ⟨hd, hi, ht⟩ := hout
      obtain ⟨⟨r', s'⟩, hp, hc', hpos, rest, hv', hlen, hout'⟩ := WP.spec_imp_exists
        (code.pop_with_type.realizes s outer segment t (by simpa [hv] using hvals)
          (by simpa [Body.Control.base, hc] using hbase))
      dsimp only at hc' hpos hv' hlen hout'
      cases r' with
      | Err e =>
          simp [code.read_local_tee, hr, hp, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Body.Scalar.IndexPost]
      | Ok popped =>
          have hcap : s'.vals.val.length < Usize.max := by
            simp only [hv', hvals, List.length_append] at *
            omega
          obtain ⟨s'', hpush, hv'', hc'', hpos'⟩ := WP.spec_imp_exists
            (code.push_val.spec s' (.Val t) hcap)
          have hpop : ∀ ts, Body.Stack.Realizes (Body.Control.polymorphic st) rest ts →
              Body.Stack.Realizes (Body.Control.polymorphic st) segment (ts ++ [Translation.valueType t]) := by
            simpa [Body.Control.polymorphic, hc] using hout'.2
          have htyping := (Body.ResumePrefix.after_pop htyped hpop).finish hC.wf
            (.LOCAL_TEE (.mk_uN idx.val)) [t] (.instr_case_45 _ (Translation.Environment.index_wf idx))
            (hC.local_tee idx t hi ht)
          rw [WP.spec_equiv_exists]
          refine ⟨(.Ok idx, s''), ?_, ?_⟩
          · simp [code.read_local_tee, hr, hp, hpush, core.result.Result.Insts.CoreOpsTry.branch]
          · intro ix heq
            cases heq
            exact ⟨by simpa [hpos', hpos] using hd, hc''.trans (hc'.trans hc), rest ++ [.Val t],
              by simpa [hv', List.append_assoc] using hv'', by simpa using Nat.add_le_add_right hlen 1,
              by simpa using htyping⟩

theorem code.read_global_get.prefix {inputs : List valtype} (st : code.OpIterState) (data : Slice U8)
    (env : metadata.Env) (ctx : code.Context) (outer segment : List code.StackType)
    (hvals : st.vals.val = outer ++ segment) (hsize : st.vals.val.length < Usize.max)
    (C : context) (hC : Translation.Environment.Matches env ctx C) (ops : List instr)
    (htyped : Body.TypedPrefix C inputs ops (Body.Control.polymorphic st) segment) :
    code.read_global_get st data env ⦃ Body.Scalar.IndexPost inputs data st outer segment C ops
      (fun idx => .GLOBAL_GET (.mk_uN idx.val)) ⦄ := by
  obtain ⟨⟨r, s⟩, hr, hv, hc, hout⟩ := WP.spec_imp_exists (code.take_global.spec st data env)
  dsimp only at hv hc hout
  cases r with
  | Err e =>
      simp [code.read_global_get, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Body.Scalar.IndexPost]
  | Ok pair =>
      obtain ⟨idx, t⟩ := pair
      obtain ⟨hd, hi, ht⟩ := hout
      obtain ⟨s', hp, hv', hc', hpos⟩ := WP.spec_imp_exists
        (code.push_val.spec s (.Val t.valtype) (by simpa [hv] using hsize))
      have htyping := (Body.ResumePrefix.of_prefix htyped).finish hC.wf
        (.GLOBAL_GET (.mk_uN idx.val)) [t.valtype] (.instr_case_46 _ (Translation.Environment.index_wf idx))
        (hC.global_get idx t hi ht)
      rw [WP.spec_equiv_exists]
      refine ⟨(.Ok idx, s'), ?_, ?_⟩
      · simp [code.read_global_get, hr, hp, core.result.Result.Insts.CoreOpsTry.branch]
      · intro ix heq
        cases heq
        exact ⟨by simpa [hpos] using hd, hc'.trans hc, segment ++ [.Val t.valtype],
          by simpa [hv, hvals, List.append_assoc] using hv', by simp, by simpa using htyping⟩

theorem code.read_global_set.prefix {inputs : List valtype} (st : code.OpIterState) (data : Slice U8)
    (env : metadata.Env) (ctx : code.Context) (outer segment : List code.StackType)
    (hvals : st.vals.val = outer ++ segment) (hbase : (Body.Control.base st).val = outer.length)
    (C : context) (hC : Translation.Environment.Matches env ctx C) (ops : List instr)
    (htyped : Body.TypedPrefix C inputs ops (Body.Control.polymorphic st) segment) :
    code.read_global_set st data env ⦃ Body.Scalar.IndexPost inputs data st outer segment C ops
      (fun idx => .GLOBAL_SET (.mk_uN idx.val)) ⦄ := by
  obtain ⟨⟨r, s⟩, hr, hv, hc, hout⟩ := WP.spec_imp_exists (code.take_global.spec st data env)
  dsimp only at hv hc hout
  cases r with
  | Err e =>
      simp [code.read_global_set, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Body.Scalar.IndexPost]
  | Ok pair =>
      obtain ⟨idx, t⟩ := pair
      obtain ⟨hd, hi, ht⟩ := hout
      cases hm : t.mutability with
      | Const =>
          simp [code.read_global_set, hr, hm, core.result.Result.Insts.CoreOpsTry.branch,
            Body.Scalar.IndexPost]
      | Var =>
          obtain ⟨⟨r', s'⟩, hp, hc', hpos, rest, hv', hlen, hout'⟩ := WP.spec_imp_exists
            (code.pop_with_type.realizes s outer segment t.valtype (by simpa [hv] using hvals)
              (by simpa [Body.Control.base, hc] using hbase))
          dsimp only at hc' hpos hv' hlen hout'
          cases r' with
          | Err e =>
              simp [code.read_global_set, hr, hp, hm, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Body.Scalar.IndexPost]
          | Ok popped =>
              have hpop : ∀ ts, Body.Stack.Realizes (Body.Control.polymorphic st) rest ts →
                  Body.Stack.Realizes (Body.Control.polymorphic st) segment (ts ++ [Translation.valueType t.valtype]) := by
                simpa [Body.Control.polymorphic, hc] using hout'.2
              have htyping := (Body.ResumePrefix.after_pop htyped hpop).finish hC.wf
                (.GLOBAL_SET (.mk_uN idx.val)) [] (.instr_case_47 _ (Translation.Environment.index_wf idx))
                (hC.global_set idx t hi ht hm)
              rw [WP.spec_equiv_exists]
              refine ⟨(.Ok idx, s'), ?_, ?_⟩
              · simp [code.read_global_set, hr, hp, hm, core.result.Result.Insts.CoreOpsTry.branch]
              · intro ix heq
                cases heq
                exact ⟨by simpa [hpos] using hd, hc'.trans hc, rest, hv', by omega,
                  by simpa using htyping⟩

end Itasca

end
