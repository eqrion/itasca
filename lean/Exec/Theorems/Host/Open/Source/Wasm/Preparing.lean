import Exec.Theorems.Host.Open.Source.State.StateGuard
import Exec.Theorems.Host.Open.Source.Control.Publication
import Exec.Spec.Open.ExecutionTraces
import Exec.Theorems.Host.Open.Source.State.RootSelection
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

theorem SourceRootInvokeReady.tick_store {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {select : Selector} {code : Store.CodeInterpretation}
    {native next : State M} {exec : runtime.interp.Execution} {address : runtime.FuncAddr}
    {signature : Itasca.types.FuncType} {args : Slice runtime.Value} {results : alloc.vec.Vec runtime.Value}
    {phase : InvokePhase M Unit}
    (ready : SourceRootInvokeReady allocator (inert memory) view code exec native.store () Spec.invocationFrame address signature args results phase)
    (mode : native.mode=.preparing phase)
    (actual : tick memory floats allocator select native=.ok (.cont next)) : next.store=native.store := by
  cases ready with
  | rejected error kind notTyped | resource error afterExec typed cause=>
    simp only [tick,mode,Result.ok.injEq,ControlFlow.cont.injEq] at actual
    exact (congrArg State.store actual).symm
  | waiting prepared token phase preparedEmpty typed ready=>
    cases ready with
    | rejected answer error status sameStore cause | defined answer entry status sameStore machine owned ambientEq step=>
      simp only [tick,mode,acceptCall,Result.ok.injEq,ControlFlow.cont.injEq] at actual
      exact (congrArg State.store actual).symm.trans sameStore
    | host ready nextToken identity copied defaults function functionAt kind signatureAt empty scratch owned capacity argumentsEq argumentsTyped=>
      simp only [tick,mode,acceptCall,Result.ok.injEq,ControlFlow.cont.injEq] at actual
      exact (congrArg State.store actual).symm

end Exec.Theorems.OpenReentrantControl
