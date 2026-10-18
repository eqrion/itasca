import Exec.Interp.StructuredMachine.Advance
import Exec.Interp.StructuredMachine.OrdinaryExecution
import Exec.Abs.Supported.CumulativeStep
namespace Exec.Interp.StructuredMachine
open Aeneas Aeneas.Std


/-- Exact ordinary runtime footprints and a checked cumulative source step
preserve the full active/suspended machine and every ownership/code bound. -/
theorem ordinary_cumulative_step {emission : FunctionEmission} {allowed : instr → Prop}
    (language : Abs.Supported.Language allowed) {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    {store nextStore : runtime.store.Store M} {exec after : runtime.interp.Execution}
    (ambient : frame) (source updatedSource : Abs.AFrame) (rest : List Abs.AFrame)
    (expected : List valtype) (beforePC : Nat) (beforePending : Bool)
    (machine : Execution emission (Abs.SupportedState allowed) view code store exec ⟨Store.decodeStore view code store,ambient,source::rest,[]⟩ expected beforePC beforePending)
    (stores : FrameStoreMetadata store nextStore)
    (raw : runtime.interp.Frame) (index : Usize) (pc : U32)
    (last : index.val+1=exec.frames.length) (lookup : exec.frames.val[index.val]?=some raw)
    {compiled C targets next output pending}
    (program : FrameProgram store raw compiled (source.locals.map Code.valueType) source.resultTypes C.FUNCS)
    (point : ControlPoint emission (Store.decodeStore view code nextStore) {raw with pc:=pc} updatedSource compiled C targets next output pending)
    (slots : FrameSlots after {raw with pc:=pc} updatedSource)
    (metadata : FrameMetadata source updatedSource)
    (effect : {after with slots:=exec.slots}={exec with frames:=exec.frames.set index {raw with pc:=pc}})
    (preserved : SlotPrefix raw.base.val exec.slots.val after.slots.val)
    (transition : Abs.Cumulative.Step ⟨Store.decodeStore view code store,ambient,source::rest,[]⟩
      (.next ⟨Store.decodeStore view code nextStore,ambient,updatedSource::rest,[]⟩)) :
    Advance emission (Abs.SupportedState allowed) Abs.Ownership.StatefulOwned view code nextStore after expected compiled.code.length beforePC beforePending
      ⟨Store.decodeStore view code store,ambient,source::rest,[]⟩ := by
  have typed := transition.next_typed_supported language machine.typed machine.core
  have covered := transition.next_covered_supported language machine.typed machine.core
  have extension := transition.next_extends_supported language machine.typed machine.core
  refine ⟨pc.val,pending,_,?_,ConcreteSim.of_source _ _ _ _ _ (transition.next_simulation_supported language machine.typed machine.core),
    fun _ h => transition.next_owned_supported language machine.typed machine.core h,rfl,
    fun _ h => transition.next_bound_supported language machine.typed machine.core h⟩
  exact StructuredMachine.Execution.ordinary view code ambient source updatedSource rest expected beforePC beforePending machine stores
    extension raw index pc last lookup program point slots metadata effect preserved typed covered
end Exec.Interp.StructuredMachine
