import Itasca.Runtime.Interp.Machine.Progress.OrdinaryExecution
import Itasca.Runtime.SourceMachine.Simd.Step

/-!
Actual SIMD frame effects preserve the complete stack of compiled callers. Source typing, supported syntax, ownership, and source bounds follow from the checked source SIMD step rather than additional runtime postulates.

Main declarations: `Execution.simd`. A direct consumer is `Interp.Machine.Simd.ConstantFrame`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas.Std

/-- Actual SIMD frame effects preserve the complete stack of compiled callers.
Source typing, supported syntax, ownership, and source bounds follow from the
checked source SIMD step rather than additional runtime postulates. -/
theorem Execution.simd {M : Type}
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    {store nextStore : runtime.store.Store M} {exec after : runtime.interp.Execution}
    (ambient : frame) (source updated : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (expected : List valtype) (beforePC : Nat) (beforePending : Bool)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,source::rest,[]⟩ expected beforePC beforePending)
    (stores : FrameStoreMetadata store nextStore)
    (raw : runtime.interp.Frame) (index : Usize) (pc : U32)
    (last : index.val+1 = exec.frames.length) (lookup : exec.frames.val[index.val]? = some raw)
    {compiled C targets next output}
    (program : FrameProgram store raw compiled (source.locals.map Compiler.valueType) source.resultTypes C.FUNCS)
    (point : FramePoint (Store.decodeStore view code nextStore) {raw with pc := pc}
      updated compiled C targets next output)
    (slots : FrameSlots after {raw with pc := pc} updated)
    (metadata : FrameMetadata source updated)
    (effect : {after with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}})
    (preserved : SlotPrefix raw.base.val exec.slots.val after.slots.val)
    (step : SourceMachine.Simd.Step ⟨Store.decodeStore view code store,ambient,source::rest,[]⟩
      (.next ⟨Store.decodeStore view code nextStore,ambient,updated::rest,[]⟩)) :
    Execution view code nextStore after
      ⟨Store.decodeStore view code nextStore,ambient,updated::rest,[]⟩ expected pc.val false ∧
    ConcreteSim compiled.code.length beforePC pc.val beforePending false
      ⟨Store.decodeStore view code store,ambient,source::rest,[]⟩
      ⟨Store.decodeStore view code nextStore,ambient,updated::rest,[]⟩ ∧
    (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds ⟨Store.decodeStore view code store,ambient,source::rest,[]⟩ →
      SourceMachine.Ownership.StatefulOwned bounds ⟨Store.decodeStore view code nextStore,ambient,updated::rest,[]⟩) ∧
    (∀ bound, SourceMachine.CodeBound bound ⟨Store.decodeStore view code store,ambient,source::rest,[]⟩ →
      SourceMachine.CodeBound bound ⟨Store.decodeStore view code nextStore,ambient,updated::rest,[]⟩) := by
  refine ⟨?_,ConcreteSim.of_source _ _ _ _ _ (step.next_simulation machine.typed),
    fun _ owned => step.next_owned owned,fun _ bounded => step.next_bound bounded⟩
  exact machine.ordinary view code ambient source updated rest expected beforePC beforePending stores
    (step.next_extension machine.typed) raw index pc last lookup program (.ready point) slots metadata effect preserved
    (step.next_typed machine.typed) (step.next_supported machine.core)

end Itasca.Runtime.Interp.Machine
