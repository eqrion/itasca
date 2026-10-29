import Itasca.Runtime.Interp.Machine.Progress.OrdinaryStack
import Itasca.Runtime.SourceMachine.Core.Step
import Itasca.Runtime.SourceMachine.Numeric.Transition
import Itasca.Runtime.SourceMachine.StepSafety
import Itasca.Runtime.SourceMachine.Core.Pure

/-!
Checked local effects assemble into the mutable whole-machine invariant. Typing and syntax facts here are supplied by the independent abstract step proof; the concrete prefix/frame effects preserve every suspended caller.

Main declarations: `Execution.ordinary`. A direct consumer is `Interp.Machine.Memory`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std

/-- Checked local effects assemble into the mutable whole-machine invariant.
Typing and syntax facts here are supplied by the independent abstract step
proof; the concrete prefix/frame effects preserve every suspended caller. -/
theorem Execution.ordinary {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    {store nextStore : runtime.store.Store M} {exec after : runtime.interp.Execution}
    (ambient : frame) (source updatedSource : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (expected : List valtype) (beforePC : Nat) (beforePending : Bool)
    (machine : Execution view code store exec ⟨Store.decodeStore view code store,ambient,source::rest,[]⟩ expected beforePC beforePending)
    (stores : FrameStoreMetadata store nextStore)
    (extension : Extend_store (Store.decodeStore view code store) (Store.decodeStore view code nextStore))
    (raw : runtime.interp.Frame) (index : Usize) (pc : U32)
    (last : index.val+1 = exec.frames.length) (lookup : exec.frames.val[index.val]? = some raw)
    {compiled C targets next output pending}
    (program : FrameProgram store raw compiled (source.locals.map Compiler.valueType) source.resultTypes C.FUNCS)
    (point : ControlPoint (Store.decodeStore view code nextStore) {raw with pc := pc} updatedSource compiled C targets next output pending)
    (slots : FrameSlots after {raw with pc := pc} updatedSource)
    (metadata : FrameMetadata source updatedSource)
    (effect : {after with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}})
    (preserved : SlotPrefix raw.base.val exec.slots.val after.slots.val)
    (typed : SourceMachine.CoreTyped ⟨Store.decodeStore view code nextStore,ambient,updatedSource::rest,[]⟩)
    (covered : SourceMachine.SupportedState ⟨Store.decodeStore view code nextStore,ambient,updatedSource::rest,[]⟩) :
    Execution view code nextStore after ⟨Store.decodeStore view code nextStore,ambient,updatedSource::rest,[]⟩ expected pc.val pending := by
  have top : exec.frames.val.getLast? = some raw := by
    rw [List.getLast?_eq_getElem?]
    have position : exec.frames.val.length-1 = index.val := by change exec.frames.length-1 = index.val; omega
    rw [position]
    exact lookup
  have binding := (machine.stack.top raw top).binding
  have frames : after.frames = exec.frames.set index {raw with pc := pc} := congrArg runtime.interp.Execution.frames effect
  have topAfter : after.frames.val.getLast? = some {raw with pc := pc} := by
    rw [frames,frames_set_last exec index _ last,List.getLast?_concat]
  refine ⟨rfl,typed,covered,?_,?_,?_⟩
  · exact SourceMachine.FramesReturn.replace machine.result metadata.results
  · exact machine.stack.ordinary stores extension raw index pc last lookup binding program point slots metadata effect preserved
  · exact ControlTop.updated topAfter (program.store_metadata stores) metadata ⟨targets,next,output,point⟩

end Itasca.Runtime.Interp.Machine
