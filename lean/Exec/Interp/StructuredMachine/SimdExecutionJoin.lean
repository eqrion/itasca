import Exec.Interp.StructuredMachine.OrdinaryExecution
import Exec.Abs.Simd.Coverage

namespace Exec.Interp.StructuredMachine
open Aeneas.Std

/-- Actual SIMD frame effects preserve the complete stack of compiled callers.
Source typing, supported syntax, ownership, and source bounds follow from the
checked source SIMD step rather than additional runtime postulates. -/
theorem Execution.simd {emission : FunctionEmission} {allowed : instr → Prop} {M : Type}
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    {store nextStore : runtime.store.Store M} {exec after : runtime.interp.Execution}
    (ambient : frame) (source updated : Abs.AFrame) (rest : List Abs.AFrame)
    (expected : List valtype) (beforePC : Nat) (beforePending : Bool)
    (machine : Execution emission (Abs.SupportedState allowed) view code store exec
      ⟨Store.decodeStore view code store,ambient,source::rest,[]⟩ expected beforePC beforePending)
    (stores : FrameStoreMetadata store nextStore)
    (raw : runtime.interp.Frame) (index : Usize) (pc : U32)
    (last : index.val+1 = exec.frames.length) (lookup : exec.frames.val[index.val]? = some raw)
    {compiled C targets next output}
    (program : FrameProgram store raw compiled (source.locals.map Code.valueType) source.resultTypes C.FUNCS)
    (point : FramePoint emission (Store.decodeStore view code nextStore) {raw with pc := pc}
      updated compiled C targets next output)
    (slots : FrameSlots after {raw with pc := pc} updated)
    (metadata : FrameMetadata source updated)
    (effect : {after with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}})
    (preserved : SlotPrefix raw.base.val exec.slots.val after.slots.val)
    (step : Abs.Simd.Step ⟨Store.decodeStore view code store,ambient,source::rest,[]⟩
      (.next ⟨Store.decodeStore view code nextStore,ambient,updated::rest,[]⟩)) :
    Execution emission (Abs.SupportedState allowed) view code nextStore after
      ⟨Store.decodeStore view code nextStore,ambient,updated::rest,[]⟩ expected pc.val false ∧
    ConcreteSim compiled.code.length beforePC pc.val beforePending false
      ⟨Store.decodeStore view code store,ambient,source::rest,[]⟩
      ⟨Store.decodeStore view code nextStore,ambient,updated::rest,[]⟩ ∧
    (∀ bounds, Abs.Ownership.StatefulOwned bounds ⟨Store.decodeStore view code store,ambient,source::rest,[]⟩ →
      Abs.Ownership.StatefulOwned bounds ⟨Store.decodeStore view code nextStore,ambient,updated::rest,[]⟩) ∧
    (∀ bound, Abs.CodeBound bound ⟨Store.decodeStore view code store,ambient,source::rest,[]⟩ →
      Abs.CodeBound bound ⟨Store.decodeStore view code nextStore,ambient,updated::rest,[]⟩) := by
  refine ⟨?_,ConcreteSim.of_source _ _ _ _ _ (step.next_simulation machine.typed),
    fun _ owned => step.next_owned owned,fun _ bounded => step.next_bound bounded⟩
  exact machine.ordinary view code ambient source updated rest expected beforePC beforePending stores
    (step.next_extension machine.typed) raw index pc last lookup program (.ready point) slots metadata effect preserved
    (step.next_typed machine.typed) (step.next_supported machine.core)

end Exec.Interp.StructuredMachine
