import Exec.Code.Body.Reader.Control.ReaderControlEffects
import Exec.Code.Body.Capacity.CapacityFoldWasm2
import Exec.Code.Body.Reader.Common.ReaderExtendedFullCapacity
import Exec.Code.Body.Reader.Common.ReaderOrdinaryEffects
import Exec.Code.Body.Reader.Simd.ReaderSimdEventDispatch
import Exec.Code.Local.Relations.Common.ReaderOpcode
import Exec.Code.Local.Relations.Common.BodyEncodingMisc
import Exec.Code.Body.Reader.Table.ReaderTableCapacity
import Exec.Code.Local.Callbacks.Calls.CallbackSafety
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- A successful reader step in a fully encoded body retains the exact local
layout and bounds slot growth by the canonical post-step operand stack. -/
theorem reader_executable_capacity_wasm2 {data env ctx index st source}
    (p : Wasm2.Pending data env .Wasm2 ctx.locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (encoded : Wasm2.BodyEncoding data source)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (data.val[p.start.val]'p.inbounds) before = .ok (.Ok (),out,after)) :
    CapacityStep before after out.core := by
  have allowed := encoded.next_reader_opcode p.consumed p.inbounds
  rcases allowed with ordinary | scope | isElse | isEnd | extra | floatBase | memory | indirect | table |
    stateful | prefixed | simd | select
  · exact (reader_ordinary_effects_wasm2 p ops law before after out ctx _ ordinary rfl accepted).capacity
  · exact (reader_control_effects_wasm2 ops law before after st out data env ctx index _ (.inl scope) accepted).capacity
  · exact (reader_control_effects_wasm2 ops law before after st out data env ctx index _ (.inr (.inl isElse)) accepted).capacity
  · exact (reader_control_effects_wasm2 ops law before after st out data env ctx index _ (.inr (.inr isEnd)) accepted).capacity
  · exact (reader_scalar_effects_wasm2 ops law before after st out data env ctx index _ extra accepted).capacity
  · obtain ⟨op,base,equal⟩ := float_base_opcode_of_mem floatBase
    rw [←equal] at accepted
    exact (reader_float_base_effects_wasm2 ops law before after st out data env ctx index op base accepted).capacity
  · exact reader_stateful_base_full_capacity_wasm2 p ops law before after out ctx _
      (stateful_opcode_values (.inl memory)) rfl accepted
  · rw [indirect] at accepted
    exact reader_indirect_call_full_capacity_wasm2 p ops law before after out ctx indirect accepted
  · rw [table] at accepted
    exact reader_table_capacity_wasm2 ops law before after st out data env ctx index accepted
  · exact reader_stateful_base_full_capacity_wasm2 p ops law before after out ctx _
      (stateful_opcode_values (.inr stateful)) rfl accepted
  · obtain ⟨sub,next,decoded,choice⟩ := encoded.next_misc p.consumed p.inbounds st.core.pos p.pos prefixed
    rw [prefixed] at accepted
    rcases choice with ⟨op,extension,subEq⟩ | bulk
    · exact (reader_saturating_effects_wasm2 p ops law before after out ctx op extension sub next subEq decoded
        prefixed accepted).capacity
    · exact reader_stateful_bulk_full_capacity_wasm2 p ops law before after out ctx sub next bulk prefixed decoded accepted
  · rw [simd] at accepted
    obtain ⟨event⟩ := reader_simd_event_wasm2 p ops before after out ctx
      (EnvTranslation.context env ctx) rfl simd accepted
    exact event.capacity_step law
  · rw [select] at accepted
    exact reader_typed_select_full_capacity_wasm2 p ops law before after out ctx select accepted

theorem TypedRunWasm2.executable_capacity_bound {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {data env ctx index st before after source}
    (run : TypedRunWasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env ctx index st before after)
    (encoded : Wasm2.BodyEncoding data source) :
    ∃ samples, ValidatedStacksWasm2 data env ctx index st samples ∧
      after.function.local_slots = before.function.local_slots ∧
      after.function.slot_count.val ≤ max before.function.slot_count.val
        (before.function.local_slots.val + maximumStackWords samples) := by
  induction run with
  | done typed closed finished =>
    exact ⟨_, .done typed closed finished, rfl, Nat.le_max_left _ _⟩
  | @step st before next out middle after typed pending start advance called rest ih =>
    obtain ⟨samples, trace, localEq, upper⟩ := ih
    have capacity := reader_executable_capacity_wasm2 pending ops law before middle out encoded called
    obtain ⟨reply, erased⟩ := Wasm2.Visitor.step_transfer
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_accepts
      data env ctx ctx rfl index .Wasm2 _ {core := {st.core with pos := next}} out before () middle called
    cases reply
    refine ⟨st.core.vals.val :: samples, .step typed pending start advance erased trace,
      localEq.trans capacity.1, ?_⟩
    have observed := trace.head_width
    have stepBound := capacity.2
    rw [observedHeight_stackWords] at stepBound
    rw [capacity.1] at upper
    change after.function.slot_count.val ≤ max before.function.slot_count.val
      (before.function.local_slots.val + max (stackWords st.core.vals.val) (maximumStackWords samples))
    omega
end Exec.Code
