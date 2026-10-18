import Exec.Interp.Calls.CallCauses

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- A rejected direct call records the fetched instruction, resolved callee,
exact caller-PC update and callee base, and the concrete rejection cause. -/
def DirectCallCause {A M P : Type} (allocator : runtime.platform.Alloc A)
    (hooks : runtime.platform.Platform P M) (before : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (frameIndex : Usize)
    (raw : runtime.interp.Frame) (caller : runtime.store.Instance)
    (callerCode : runtime.bytecode.CompiledFunction) (error : runtime.ExecError) : Prop :=
  ∃ (target offset pc : U32) (address : runtime.FuncAddr) (base : Usize)
    (function : runtime.store.Function) (instanceIndex functionIndex : Usize)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction),
    callerCode.code.val[raw.pc.val]? = some (.Call target offset) ∧
    caller.funcs.val[target.val]? = some address ∧
    store.funcs.val[address.index.val]? = some function ∧
    function.code = .Wasm instanceIndex functionIndex ∧
    store.instances.val[instanceIndex.val]? = some inst ∧
    inst.module.functions.val[functionIndex.val]? = some compiled ∧
    base.val = raw.base.val + offset.val ∧ pc.val = raw.pc.val + 1 ∧
    CallCause allocator hooks
      { before with frames := before.frames.set frameIndex { raw with pc := pc } }
      store platform base compiled error

end Exec.Interp
