import Itasca.Runtime.Interp.Relations.StepRecording
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt

/-- Initial-call recording selects a host site from the actual pre-call store.
A Wasm call contributes no event; its subsequent dispatches have their own sites. -/
def callHostEvents {M P : Type} (store : runtime.store.Store M) (address : runtime.FuncAddr)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) : List HostEvent :=
  match store.funcs.val[address.index.val]? with
  | some function => match function.code with
    | .Host _ => hostCallEvents address out
    | .Wasm .. => []
  | none => []

def recordedCall {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (base : Usize) (prior : List HostEvent) :=
  Platform.Recording.run (runtime.interp.call memory hooks floats allocator exec store platform address base)
    (callHostEvents store address) prior

theorem recordedCall_returned {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (base : Usize) (prior : List HostEvent) (out) (trace : List HostEvent) :
    recordedCall memory hooks floats allocator exec store platform address base prior = .ok (out,trace) ↔
      runtime.interp.call memory hooks floats allocator exec store platform address base = .ok out ∧
      trace = prior ++ callHostEvents store address out :=
  Platform.Recording.returned _ _ _ _ _

theorem callHostEvents_host {M P : Type} {store : runtime.store.Store M} {address : runtime.FuncAddr}
    {function : runtime.store.FuncInst} {identity : U64}
    (found : store.funcs.val[address.index.val]?=some function) (host : function.code=.Host identity)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) :
    callHostEvents store address out = hostCallEvents address out := by
  simp only [callHostEvents,found,host]

theorem callHostEvents_wasm {M P : Type} {store : runtime.store.Store M} {address : runtime.FuncAddr}
    {function : runtime.store.FuncInst} {instanceIndex functionIndex : Usize}
    (found : store.funcs.val[address.index.val]?=some function) (defined : function.code=.Wasm instanceIndex functionIndex)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) :
    callHostEvents store address out = [] := by
  simp only [callHostEvents,found,defined]
end Itasca.Runtime.Interp
