import Exec.Interp.StructuredMachine.FloatCoreAdapter
import Exec.Interp.StructuredMachine.OrdinaryExecution
import Exec.Interp.FloatCore.OrdinaryStack
import Exec.Abs.Core.StatePreservation
namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Checked local effects assemble into the mutable whole-machine invariant.
Typing and syntax facts here are supplied by the independent abstract step
proof; the concrete prefix/frame effects preserve every suspended caller. -/
theorem FloatCoreExecution.ordinary {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    {store nextStore : runtime.store.Store M} {exec after : runtime.interp.Execution}
    (ambient : frame) (source updatedSource : Abs.AFrame) (rest : List Abs.AFrame)
    (expected : List valtype) (beforePC : Nat) (beforePending : Bool)
    (machine : FloatCoreExecution view code store exec ⟨Store.decodeStore view code store,ambient,source::rest,[]⟩ expected beforePC beforePending)
    (stores : FrameStoreMetadata store nextStore)
    (extension : Extend_store (Store.decodeStore view code store) (Store.decodeStore view code nextStore))
    (raw : runtime.interp.Frame) (index : Usize) (pc : U32)
    (last : index.val+1 = exec.frames.length) (lookup : exec.frames.val[index.val]? = some raw)
    {compiled C targets next output pending}
    (program : FrameProgram store raw compiled (source.locals.map Code.valueType) source.resultTypes C.FUNCS)
    (point : FloatCoreControlPoint (Store.decodeStore view code nextStore) {raw with pc := pc} updatedSource compiled C targets next output pending)
    (slots : FrameSlots after {raw with pc := pc} updatedSource)
    (metadata : FrameMetadata source updatedSource)
    (effect : {after with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}})
    (preserved : SlotPrefix raw.base.val exec.slots.val after.slots.val)
    (typed : Abs.CoreTyped ⟨Store.decodeStore view code nextStore,ambient,updatedSource::rest,[]⟩)
    (covered : Abs.FloatCoreState ⟨Store.decodeStore view code nextStore,ambient,updatedSource::rest,[]⟩) :
    FloatCoreExecution view code nextStore after ⟨Store.decodeStore view code nextStore,ambient,updatedSource::rest,[]⟩ expected pc.val pending := by
  apply StructuredMachine.FloatCoreAdapter.execution_iff.mpr
  exact StructuredMachine.Execution.ordinary view code ambient source updatedSource rest expected beforePC beforePending
    (StructuredMachine.FloatCoreAdapter.execution_iff.mp machine) stores extension raw index pc last lookup program
    (StructuredMachine.FloatCoreAdapter.control_iff.mp point) slots metadata effect preserved typed covered

end Exec.Interp
