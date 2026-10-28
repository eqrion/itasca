import Exec.Store.Instantiation.InstantiateNoStart
import Exec.Store.Initialization.SegmentCodeMetadata
import Exec.Theorems.Composition.Entry
import Exec.Code.Local.Relations.Common.Function
import Exec.Interp.Calls.CallRefinement
import Exec.Interp.Control.StructuredPoint
import Exec.Interp.Calls.CallStack
import Exec.Interp.Machines.Slice.SliceExecution
import Exec.Interp.Machines.Slice.SliceHistory
import Exec.Interp.Relations.Readback
import Exec.Abs.Results
import Exec.Interp.Invocation.InvokeCompose
import Exec.Interp.Invocation.InvokeChecks
import Exec.Interp.Relations.Marshal
import Exec.Representation.Collection
import Exec.Interp.Relations.TypeSlots
import Exec.Interp.Relations.Ensure
import Exec.Interp.Relations.ExecutionLoop
import Exec.Interp.Machines.Slice.SliceErrors
import Exec.Interp.Invocation.InvokeDivergence
import Exec.Interp.Machines.Slice.SliceDivergence
import Exec.Interp.Relations.TypedArguments
import Exec.Spec.Invocation
import Exec.Store.Invariant.Typing
import Exec.Theorems.Instantiation.StartAmbient
import Exec.Abs.Sim.Call

namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

/-- Module-start execution uses the newly installed module and no ambient locals. -/
def moduleStartFrame {M : Type} (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) : frame :=
  ⟨[], Store.decodeInstance store inst⟩

def moduleStartConfiguration {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : U32) : config :=
  ⟨⟨Store.decodeStore view code store, moduleStartFrame store inst⟩, [.CALL (.mk_uN index.val)]⟩

theorem moduleStartFrame_wf {M : Type} (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (index : Usize) (inst : runtime.store.ModuleInst)
    (sourceSyntax : Store.StoreSyntax code store) (found : store.instances.val[index.val]? = some inst) :
    wf_frame (moduleStartFrame store inst) := by
  apply wf_frame.frame_case_
  · simp [Forall]
  · exact Store.decodeInstance_wf code index.val store inst (sourceSyntax index.val inst found)

theorem module_start_resolve {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : U32) (address : runtime.FuncAddr)
    (storeWf : wf_store (Store.decodeStore view code store))
    (frameWf : wf_frame (moduleStartFrame store inst))
    (mapped : inst.funcs.val[index.val]? = some address) :
    StepH (moduleStartConfiguration view code store inst index) []
      (ambientStartConfiguration view code store (moduleStartFrame store inst) address) := by
  apply Abs.call_resolve _ _ index.val address.index.val storeWf frameWf
  · simp only [moduleStartFrame, Store.decodeInstance, List.getElem?_map, mapped, Option.map_some]
  · scalar_tac

end Exec.Theorems
