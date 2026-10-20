import Exec.Theorems.Host.Open.Source.State.RootCall
import Exec.Theorems.Host.Open.Source.State.World
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- Root and internal host calls expose the same typed suspension interface.
The root's empty evaluation context is constructed from source typing and raw
host metadata, with the native future-world continuation already proved. -/
theorem SourceRootCallReady.select {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    {allocator : runtime.platform.Alloc A} {hooks : runtime.platform.Platform Unit M}
    (view : M → Slice U8) (code : Store.CodeInterpretation) (select : Selector)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (token : Unit)
    (ambient : frame) (ambientWf : wf_frame ambient) (address : runtime.FuncAddr)
    (signature : Itasca.types.FuncType) (arguments : List val) (phase : CallPhase M Unit)
    (guard : SourceRootCallReady allocator hooks exec store token view code ambient address signature arguments phase)
    (configurationTyped : Config_ok ⟨⟨Store.decodeStore view code store,ambient⟩,vals arguments++[.CALL_ADDR address.index.val]⟩
      (.mk_list (signature.results.val.map sourceType))) :
    SelectedSourceHost memory view code select store
      ⟨⟨Store.decodeStore view code store,ambient⟩,vals arguments++[.CALL_ADDR address.index.val]⟩
      (.mk_list (signature.results.val.map sourceType)) phase := by
  cases guard with
  | rejected answer error status sameStore cause=>trivial
  | defined answer entry status sameStore machine owned ambientEq source=>trivial
  | host ready nextToken identity args defaults function functionAt kind signatureAt empty scratch owned capacity argumentsEq argumentsTyped=>
    let pending:=rootSourcePending view code store ambient ambientWf address identity signature arguments
      (Store.decode_host_function view code store address function identity signature functionAt kind signatureAt) argumentsTyped
    refine ⟨scratch,pending,rfl,rfl,rfl,argumentsEq.symm,?_,configurationTyped,?_,?_,?_⟩
    · apply StepsH.refl
      cases configurationTyped
      assumption
    · exact Spec.UniversalQuietPrefix.refl _ (by cases configurationTyped;assumption)
    · exact root_source_continuation memory view code store ready empty address function identity signature functionAt kind signatureAt
        ambient ambientWf arguments argumentsTyped capacity
    · change HostStateRepresents store.id (sourceHostEntry select store.id identity.val arguments)
        ⟨0,select identity args.slice,identity,args.slice⟩
      rw [←argumentsEq]
      exact sourceHostEntry_represents select store.id identity args.slice owned
end Exec.Theorems.OpenReentrantControl
