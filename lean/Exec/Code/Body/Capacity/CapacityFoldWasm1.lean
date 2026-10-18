import Exec.Code.Body.Reader.Common.ReaderStepCapacityWasm1
import Exec.Code.Local.Source.ValidatedStacks
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem ValidatedStacksWasm1.head_width {data env ctx bt st samples}
    (trace : ValidatedStacksWasm1 data env ctx bt st samples) :
    stackWords st.vals.val ≤ maximumStackWords samples := by
  cases trace with
  | done => simp [maximumStackWords]
  | step => exact Nat.le_max_left _ _

theorem TypedRunWasm1.capacity_bound {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {data env ctx bt st before after source}
    (run : TypedRunWasm1 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env ctx bt st before after)
    (encoded : Wasm1.BodyEncoding data source) (supported : Forall Abs.SliceInstr source) :
    ∃ samples, ValidatedStacksWasm1 data env ctx bt st samples ∧
      after.function.local_slots = before.function.local_slots ∧
      after.function.slot_count.val ≤ max before.function.slot_count.val
        (before.function.local_slots.val + maximumStackWords samples) := by
  induction run with
  | done typed closed finished =>
    exact ⟨_, .done typed closed finished, rfl, Nat.le_max_left _ _⟩
  | @step st before next out middle after typed pending start advance called rest ih =>
    obtain ⟨samples, trace, localEq, upper⟩ := ih
    have allowed := encoded.next_slice_opcode supported pending.consumed pending.inbounds
    have capacity := reader_step_capacity_wasm1 ops law before middle _ out data env ctx _ allowed called
    have erased := code.step.accepted_erase
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} out data env ctx _ before middle called
    refine ⟨st.vals.val :: samples, .step typed pending start advance erased trace,
      localEq.trans capacity.1, ?_⟩
    have observed := trace.head_width
    have stepBound := capacity.2
    rw [observedHeight_stackWords] at stepBound
    rw [capacity.1] at upper
    change after.function.slot_count.val ≤ max before.function.slot_count.val
      (before.function.local_slots.val + max (stackWords st.vals.val) (maximumStackWords samples))
    omega
end Exec.Code
