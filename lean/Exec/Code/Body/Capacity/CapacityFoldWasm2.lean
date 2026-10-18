import Exec.Code.Body.Reader.Common.ReaderStepCapacityWasm2
import Exec.Code.Local.Source.ValidatedStacks
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem ValidatedStacksWasm2.head_width {data env ctx index st samples}
    (trace : ValidatedStacksWasm2 data env ctx index st samples) :
    stackWords st.core.vals.val ≤ maximumStackWords samples := by
  cases trace with
  | done => simp [maximumStackWords]
  | step => exact Nat.le_max_left _ _

theorem TypedRunWasm2.capacity_bound {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {data env ctx index st before after source}
    (run : TypedRunWasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env ctx index st before after)
    (encoded : Wasm2.BodyEncoding data source) (supported : Forall Abs.SliceInstr source) :
    ∃ samples, ValidatedStacksWasm2 data env ctx index st samples ∧
      after.function.local_slots = before.function.local_slots ∧
      after.function.slot_count.val ≤ max before.function.slot_count.val
        (before.function.local_slots.val + maximumStackWords samples) := by
  induction run with
  | done typed closed finished =>
    exact ⟨_, .done typed closed finished, rfl, Nat.le_max_left _ _⟩
  | @step st before next out middle after typed pending start advance called rest ih =>
    obtain ⟨samples, trace, localEq, upper⟩ := ih
    have allowed := encoded.next_slice_opcode supported pending.consumed pending.inbounds
    have capacity := reader_step_capacity_wasm2 ops law before middle _ out data env ctx index _ allowed called
    obtain ⟨reply, erased⟩ := Wasm2.Visitor.step_transfer
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_accepts
      data env ctx ctx rfl index _ {core := {st.core with pos := next}} out before () middle called
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
