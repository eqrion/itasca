import Itasca.Runtime.Interp.Machine.Frames.StackPreservation
import Itasca.Runtime.Interp.Machine.Execution
import Itasca.Runtime.Interp.Control.BrTableSource
import Itasca.Runtime.Interp.Relations.PrefixDispatch
import Itasca.Runtime.SourceMachine.Core.Trap
import Itasca.Runtime.SourceMachine.Numeric.Transition
import Itasca.Runtime.SourceMachine.Bound
import Itasca.Runtime.SourceMachine.Ownership.Extension
import Itasca.Runtime.SourceMachine.Stateful.TableSet
import Itasca.Runtime.SourceMachine.Supported.CumulativeStep

/-!
Sections, each formerly its own module: OrdinaryStack, OrdinaryExecution, Advance, SupportedAdvance.
-/

/-! ## OrdinaryStack -/

section

/-!
Ordinary bytecode changes only the active source's live values and code. Its observed prefix law preserves all suspended frames at once.

Main declarations: `FrameStackRel.ordinary`. A direct consumer is `Interp.Machine.Emission.Unreachable`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std

/-- Ordinary bytecode changes only the active source's live values and code.
Its observed prefix law preserves all suspended frames at once. -/
theorem FrameStackRel.ordinary {M : Type} {store nextStore : runtime.store.Store M}
    {sourceStore nextSourceStore : _root_.store}
    {exec after : runtime.interp.Execution} {source updatedSource : SourceMachine.AFrame} {rest : List SourceMachine.AFrame}
    (relation : FrameStackRel store sourceStore exec (source :: rest))
    (stores : FrameStoreMetadata store nextStore) (extension : Extend_store sourceStore nextSourceStore)
    (raw : runtime.interp.Frame) (index : Usize) (pc : U32)
    (last : index.val + 1 = exec.frames.length)
    (lookup : exec.frames.val[index.val]? = some raw)
    (binding : FrameBinding store exec raw source)
    {compiled C targets next output pending}
    (program : FrameProgram store raw compiled (source.locals.map Compiler.valueType) source.resultTypes C.FUNCS)
    (point : ControlPoint nextSourceStore { raw with pc := pc } updatedSource compiled C targets next output pending)
    (slots : FrameSlots after { raw with pc := pc } updatedSource)
    (metadata : FrameMetadata source updatedSource)
    (effect : { after with slots := exec.slots } =
      { exec with frames := exec.frames.set index { raw with pc := pc } })
    (preserved : SlotPrefix raw.base.val exec.slots.val after.slots.val) :
    FrameStackRel nextStore nextSourceStore after (updatedSource :: rest) := by
  have frames : after.frames = exec.frames.set index { raw with pc := pc } :=
    congrArg runtime.interp.Execution.frames effect
  have identity : after.store = exec.store := by
    have h := congrArg runtime.interp.Execution.store effect
    exact h
  have capacity : exec.slots.length ≤ after.slots.length := by
    change exec.slots.val.length ≤ after.slots.val.length
    rw [preserved.length]
  have top : exec.frames.val.getLast? = some raw := by
    rw [List.getLast?_eq_getElem?]
    have position : exec.frames.val.length - 1 = index.val := by change exec.frames.length - 1 = index.val; omega
    rw [position]
    exact lookup
  have framesVal : after.frames.val = exec.frames.val.dropLast ++ [{ raw with pc := pc }] := by
    rw [frames]
    exact frames_set_last exec index _ last
  refine relation.step_active stores extension raw { raw with pc := pc } top framesVal rfl metadata.results identity capacity
    (fun position bits represented below => preserved.region position bits represented below) ?_
  refine ⟨?_, slots, compiled, C, targets, next, output, pending, ?_, point⟩
  · obtain ⟨inst, fn, code, signature, oldIdentity, oldMember, hi, hf, hw, hc, hs, hm, hr, hl, bound⟩ := binding.store_metadata stores
    refine ⟨inst, fn, code, signature, identity.trans oldIdentity, ?_, hi, ?_, hw, hc, hs, ?_, ?_, ?_, bound.trans capacity⟩
    · rw [framesVal]
      simp
    · simpa only [metadata.address] using hf
    · exact metadata.module.trans hm
    · exact metadata.results.trans hr
    · exact metadata.locals.trans hl
  · exact ⟨(program.store_metadata stores).lookup, program.checked, program.fetchBound,
      program.localSlots.trans (congrArg Compiler.slots metadata.locals).symm,
      by simpa only [metadata.results] using program.epilogue⟩

end Itasca.Runtime.Interp.Machine

end

/-! ## OrdinaryExecution -/

section

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

end

/-! ## Advance -/

section

/-!
A returned mutable-machine step retains the complete current state, source simulation and reference provenance for every initial issued bound.

Main declarations: `Advance`. A direct consumer is `Interp.Machine.Progress.OrdinaryAdvance`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std

/-- A returned mutable-machine step retains the complete current state,
source simulation and reference provenance for every initial issued bound. -/
def Advance
 {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (exec : runtime.interp.Execution)
    (expected : List valtype) (codeLength pc : Nat) (pending : Bool) (before : SourceMachine.AState) : Prop :=
  ∃ nextPC nextPending after,
    Execution view code store exec after expected nextPC nextPending ∧
    ConcreteSim codeLength pc nextPC pending nextPending before after ∧
    (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds before → SourceMachine.Ownership.StatefulOwned bounds after) ∧ after.ambient = before.ambient ∧
    (∀ bound, SourceMachine.CodeBound bound before → SourceMachine.CodeBound bound after)

 theorem Advance.of_frame  {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} {exec : runtime.interp.Execution}
    {expected : List valtype} {codeLength pc : Nat} {pending : Bool} {before : SourceMachine.AState}
    {nextPC : U32} {nextPending : Bool} {after : SourceMachine.AState}
    (machine : Execution view code store exec after expected nextPC.val nextPending)
    (simulation : ConcreteSim codeLength pc nextPC.val pending nextPending before after)
    (ownership : ∀ bounds, SourceMachine.Ownership.StatefulOwned bounds before → SourceMachine.Ownership.StatefulOwned bounds after)
    (ambient : after.ambient = before.ambient)
    (bounded : ∀ bound, SourceMachine.CodeBound bound before → SourceMachine.CodeBound bound after) :
    Advance view code store exec expected codeLength pc pending before :=
  ⟨nextPC.val,nextPending,after,machine,simulation,ownership,ambient,bounded⟩
end Itasca.Runtime.Interp.Machine

end

/-! ## SupportedAdvance -/

section

/-!
Exact ordinary runtime footprints and a checked cumulative source step preserve the full active/suspended machine and every ownership/code bound.

Main declarations: `ordinary_cumulative_step`. A direct consumer is `Interp.Machine.Calls.IndirectSelected`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std


/-- Exact ordinary runtime footprints and a checked cumulative source step
preserve the full active/suspended machine and every ownership/code bound. -/
theorem ordinary_cumulative_step
 {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    {store nextStore : runtime.store.Store M} {exec after : runtime.interp.Execution}
    (ambient : frame) (source updatedSource : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (expected : List valtype) (beforePC : Nat) (beforePending : Bool)
    (machine : Execution view code store exec ⟨Store.decodeStore view code store,ambient,source::rest,[]⟩ expected beforePC beforePending)
    (stores : FrameStoreMetadata store nextStore)
    (raw : runtime.interp.Frame) (index : Usize) (pc : U32)
    (last : index.val+1=exec.frames.length) (lookup : exec.frames.val[index.val]?=some raw)
    {compiled C targets next output pending}
    (program : FrameProgram store raw compiled (source.locals.map Compiler.valueType) source.resultTypes C.FUNCS)
    (point : ControlPoint (Store.decodeStore view code nextStore) {raw with pc:=pc} updatedSource compiled C targets next output pending)
    (slots : FrameSlots after {raw with pc:=pc} updatedSource)
    (metadata : FrameMetadata source updatedSource)
    (effect : {after with slots:=exec.slots}={exec with frames:=exec.frames.set index {raw with pc:=pc}})
    (preserved : SlotPrefix raw.base.val exec.slots.val after.slots.val)
    (transition : SourceMachine.Cumulative.Step ⟨Store.decodeStore view code store,ambient,source::rest,[]⟩
      (.next ⟨Store.decodeStore view code nextStore,ambient,updatedSource::rest,[]⟩)) :
    Advance view code nextStore after expected compiled.code.length beforePC beforePending
      ⟨Store.decodeStore view code store,ambient,source::rest,[]⟩ := by
  have typed := transition.next_typed_supported machine.typed machine.core
  have covered := transition.next_covered_supported machine.typed machine.core
  have extension := transition.next_extends_supported machine.typed machine.core
  refine ⟨pc.val,pending,_,?_,ConcreteSim.of_source _ _ _ _ _ (transition.next_simulation_supported machine.typed machine.core),
    fun _ h => transition.next_owned_supported machine.typed machine.core h,rfl,
    fun _ h => transition.next_bound_supported machine.typed machine.core h⟩
  exact Machine.Execution.ordinary view code ambient source updatedSource rest expected beforePC beforePending machine stores
    extension raw index pc last lookup program point slots metadata effect preserved typed covered
end Itasca.Runtime.Interp.Machine

end
