import Exec.Theorems.Instantiation.InstantiateStartAmbient
import Exec.Abs.Sim.Call

namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

/-- Module-start execution uses the newly installed module and no ambient locals. -/
def moduleStartFrame {M : Type} (store : runtime.store.Store M) (inst : runtime.store.Instance) : frame :=
  ⟨[], Store.decodeInstance store inst⟩

def moduleStartConfiguration {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.Instance) (index : U32) : config :=
  ⟨⟨Store.decodeStore view code store, moduleStartFrame store inst⟩, [.CALL (.mk_uN index.val)]⟩

theorem moduleStartFrame_wf {M : Type} (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (index : Usize) (inst : runtime.store.Instance)
    (sourceSyntax : Store.StoreSyntax code store) (found : store.instances.val[index.val]? = some inst) :
    wf_frame (moduleStartFrame store inst) := by
  apply wf_frame.frame_case_
  · simp [Forall]
  · exact Store.decodeInstance_wf code index.val store inst (sourceSyntax index.val inst found)

theorem module_start_resolve {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.Instance) (index : U32) (address : runtime.FuncAddr)
    (storeWf : wf_store (Store.decodeStore view code store))
    (frameWf : wf_frame (moduleStartFrame store inst))
    (mapped : inst.funcs.val[index.val]? = some address) :
    StepH (moduleStartConfiguration view code store inst index) []
      (ambientStartConfiguration view code store (moduleStartFrame store inst) address) := by
  apply Abs.call_resolve _ _ index.val address.index.val storeWf frameWf
  · simp only [moduleStartFrame, Store.decodeInstance, List.getElem?_map, mapped, Option.map_some]
  · scalar_tac

theorem SliceInvocationError.prepend {initial current : config} {s : _root_.store} {ambient : frame}
    {error : runtime.ExecError} (step : StepH initial [] current)
    (outcome : SliceInvocationError current s ambient error) : SliceInvocationError initial s ambient error := by
  cases error <;> simp only [SliceInvocationError] at outcome ⊢ <;> try trivial
  exact ⟨outcome.1, by simpa using StepsH.cons step outcome.2⟩

end Exec.Theorems
