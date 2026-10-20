import Exec.Spec.Open.ExecutionTraces
import Exec.Theorems.Host.Open.Source.Control.Control
import Exec.Theorems.Host.Open.Source.State.World
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp SpecExt

/-- The particular typed source suspension selected by actual preparation is
reached by source Wasm normalization followed by a visible host entry. -/
theorem selected_source_entry {M : Type} (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8) (code : Store.CodeInterpretation)
    (select : Selector) (publication : SourcePublication)
    (stop : Spec.OpenExecution.StopReason → config → Prop)
    (store : runtime.store.Store M) (source : config) (expected : resulttype)
    (ready : runtime.interp.Execution) (address : runtime.FuncAddr) (base : Usize) (identity : U64)
    (args defaults : alloc.vec.Vec runtime.Value)
    (selected : SelectedSourceHost memory view code select store source expected
      (.pending ready store () address base identity args defaults))
    (stack : List (Spec.OpenExecution.Continuation SourceControl)) :
    ∃pending : Spec.OpenHost.Pending,∃typed : Config_ok pending.initial expected,∃count,
      Spec.OpenExecution.Trace (sourceModel view publication select store.id stop) (count+1)
        ⟨source.1.1,.wasm source.1.2 source.2 expected,stack⟩
        (List.replicate count .wasm++[.hostEnter address.index.val identity.val (args.val.map sourceValue)])
        ⟨Store.decodeStore view code store,
          .host (.active (sourceHostEntry select store.id identity.val (args.val.map sourceValue))),
          .wasm ⟨pending,expected,typed⟩::stack⟩ ∧
      pending.before=Store.decodeStore view code store ∧ pending.address=address.index.val ∧
      pending.identity=identity.val ∧ pending.arguments=args.val.map sourceValue := by
  obtain ⟨scratch,pending,beforeEq,addressEq,identityEq,argsEq,path,typed,chosen,saved,representation⟩ := selected
  obtain ⟨count,normalization⟩ := Spec.OpenExecution.Trace.wasmSteps
    (sourceModel view publication select store.id stop) path expected stack
  let suspended : Spec.OpenExecution.Suspension:=⟨pending,expected,typed⟩
  have enter : Spec.OpenExecution.Transition (sourceModel view publication select store.id stop)
      ⟨pending.initial.1.1,.wasm pending.initial.1.2 pending.initial.2 expected,stack⟩
      [.hostEnter pending.address pending.identity pending.arguments]
      ⟨pending.before,.host (.active (sourceHostEntry select store.id pending.identity pending.arguments)),.wasm suspended::stack⟩ := by
    have step : Spec.OpenExecution.Transition (sourceModel view publication select store.id stop)
        ⟨pending.initial.1.1,.wasm pending.initial.1.2 pending.initial.2 expected,stack⟩
        [.hostEnter pending.address pending.identity pending.arguments]
        ⟨pending.initial.1.1,.host (.active (sourceHostEntry select store.id pending.identity pending.arguments)),.wasm suspended::stack⟩ :=
      .enter suspended rfl (Spec.OpenExecution.pending_store pending).symm rfl
    simpa only [Spec.OpenExecution.pending_store] using step
  have trace := normalization.trans (Spec.OpenExecution.Trace.next enter (.nil _))
  refine ⟨pending,typed,count,?_,beforeEq,addressEq,identityEq,argsEq⟩
  simpa only [List.append_nil,beforeEq,addressEq,identityEq,argsEq] using trace
end Exec.Theorems.OpenReentrantControl
