import Exec.Code.Body.Capacity.CapacityFoldWasm1
import Exec.Code.Body.Reader.Common.ReaderExtraFullCapacityWasm1
import Exec.Code.Body.Reader.Common.ReaderExtendedFullCapacity
import Exec.Code.Body.Reader.Float.ReaderFloatCapacity
import Exec.Code.Body.Lowering.Float.FloatWasm1Exclusion
import Exec.Code.Local.Relations.Common.ExecutableWasm1Opcodes
import Exec.Code.Body.Reader.Table.ReaderTableCapacity
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem reader_executable_capacity_wasm1 {data env ctx bt st source}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (encoded : Wasm1.BodyEncoding data source)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (data.val[p.start.val]'p.inbounds) before = .ok (.Ok (),out,after)) :
    CapacityStep before after out := by
  have allowed := encoded.next_executable_wasm1_opcode p.consumed p.inbounds
  rcases allowed with floatCore | memory | indirect | table
  · rcases floatCore with core | floatBase | prefixed
    · rcases core with slice | extra
      · exact reader_step_capacity_wasm1 ops law before after st out data env ctx _ slice accepted
      · exact reader_core_extra_full_capacity_wasm1 p ops law before after out _ extra rfl accepted
    · obtain ⟨op,base,equal⟩ := float_base_opcode_of_mem floatBase
      rw [←equal] at accepted
      exact reader_float_capacity ops law before after st out data env ctx op base accepted
    · rw [prefixed] at accepted
      exact False.elim (float_saturating_wasm1_impossible
        (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after st out data env ctx accepted)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at memory
    rcases memory with size | grow
    · have equal : (data.val[p.start.val]'p.inbounds) = 63#u8 := UScalar.eq_of_val_eq size
      rw [equal] at accepted
      exact reader_memory_size_full_capacity_wasm1 ops law before after st out data env ctx accepted
    · have equal : (data.val[p.start.val]'p.inbounds) = 64#u8 := UScalar.eq_of_val_eq grow
      rw [equal] at accepted
      exact reader_memory_grow_full_capacity_wasm1 ops law before after st out data env ctx accepted
  · rw [indirect] at accepted
    exact reader_indirect_call_full_capacity_wasm1 p ops law before after out indirect accepted
  · rw [table] at accepted
    exact reader_table_capacity_wasm1 ops law before after st out data env ctx (by simpa only [global_simps] using accepted)

theorem TypedRunWasm1.executable_capacity_bound {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {data env ctx bt st before after source}
    (run : TypedRunWasm1 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env ctx bt st before after)
    (encoded : Wasm1.BodyEncoding data source) :
    ∃ samples, ValidatedStacksWasm1 data env ctx bt st samples ∧
      after.function.local_slots = before.function.local_slots ∧
      after.function.slot_count.val ≤ max before.function.slot_count.val
        (before.function.local_slots.val + maximumStackWords samples) := by
  induction run with
  | done typed closed finished =>
    exact ⟨_, .done typed closed finished, rfl, Nat.le_max_left _ _⟩
  | @step st before next out middle after typed pending start advance called rest ih =>
    obtain ⟨samples, trace, localEq, upper⟩ := ih
    have capacity := reader_executable_capacity_wasm1 pending ops law before middle out encoded called
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
