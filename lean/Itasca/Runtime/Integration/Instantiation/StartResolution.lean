import Itasca.Runtime.Store.Instantiation.NoStart
import Itasca.Runtime.Store.Initialization.SegmentCodeMetadata
import Itasca.Runtime.Integration.Execution.Dispatch.Arguments
import Itasca.Runtime.Compiler.Local.Relations.Function.Function
import Itasca.Runtime.Interp.Calls.CallRefinement
import Itasca.Runtime.Interp.Control.StructuredPoint
import Itasca.Runtime.Interp.Calls.CallStack
import Itasca.Runtime.Interp.Machine.Frames.Reposition
import Itasca.Runtime.Interp.Machine.History.Append
import Itasca.Runtime.Interp.Relations.Readback
import Itasca.Runtime.SourceMachine.Results
import Itasca.Runtime.Interp.Invocation.Checks
import Itasca.Runtime.Interp.Relations.Marshal
import Itasca.Runtime.Representation.Collection
import Itasca.Runtime.Interp.Relations.TypeSlots
import Itasca.Runtime.Interp.Relations.Ensure
import Itasca.Runtime.Interp.Relations.ExecutionLoop
import Itasca.Runtime.Interp.Machine.Resources.CallErrors
import Itasca.Runtime.Interp.Invocation.Divergence
import Itasca.Runtime.Interp.Machine.Progress.ActiveLoop
import Itasca.Runtime.Interp.Relations.TypedArguments
import Itasca.Runtime.Spec.Invocation
import Itasca.Runtime.Store.Invariant.Typing
import Itasca.Runtime.Integration.Instantiation.StartAmbient
import Itasca.Runtime.SourceMachine.Sim.Call

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt

/-- Module-start execution uses the newly installed module and no ambient locals. -/
def moduleStartFrame {M : Type} (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) : frame :=
  ⟨[], Store.decodeInstance store inst⟩

def moduleStartConfiguration {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : U32) : config :=
  ⟨⟨Store.decodeStore view code store, moduleStartFrame store inst⟩, [.CALL (.mk_uN index.val)]⟩

theorem module_start_frame_wf {M : Type} (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (index : Usize) (inst : runtime.store.ModuleInst)
    (sourceSyntax : Store.StoreSyntax code store) (found : store.instances.val[index.val]? = some inst) :
    wf_frame (moduleStartFrame store inst) := by
  apply wf_frame.frame_case_
  · simp [Forall]
  · exact Store.decode_instance_wf code index.val store inst (sourceSyntax index.val inst found)

theorem module_start_resolve {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : U32) (address : runtime.FuncAddr)
    (storeWf : wf_store (Store.decodeStore view code store))
    (frameWf : wf_frame (moduleStartFrame store inst))
    (mapped : inst.funcs.val[index.val]? = some address) :
    StepH (moduleStartConfiguration view code store inst index) []
      (ambientStartConfiguration view code store (moduleStartFrame store inst) address) := by
  apply SourceMachine.call_resolve _ _ index.val address.index.val storeWf frameWf
  · simp only [moduleStartFrame, Store.decodeInstance, List.getElem?_map, mapped, Option.map_some]
  · scalar_tac

end Itasca.Runtime.Integration
