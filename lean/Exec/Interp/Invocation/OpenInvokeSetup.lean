import Exec.Interp.Invocation.OpenInvokeSetupEffects

namespace Exec.Interp.OpenCall
open Aeneas Aeneas.Std

/-- Checked invocation setup exposes typed argument slots and empty frames
before entering the resumable call. Every setup rejection has its actual
resource cause and retains the input store. -/
theorem prepare_invoke_checked {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst)
    (signature : Itasca.types.FuncType) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store=store.id) (hf : store.funcs.val[address.index.val]?=some function)
    (hs : store.types.val[function.signature.val]?=some signature)
    (accepted : runtime.interp.check_values memory store args signature.params.deref=.ok (.Ok ()))
    (owned : ∀value∈args.val,ValueOwnedFits store.id value)
    (post : InvokePhase M P → Prop)
    (early : ∀error,InvocationResourceCause allocator exec store signature results error →
      ∀afterExec,post (.done (.Err error,afterExec,store,platform,results)))
    (handler : ∀prepared p,prepared.store=store.id → prepared.frames.val=[] →
      ValuesAt prepared.slots.val 0 (args.val.map sourceValue) →
      prepareCall memory hooks floats allocator prepared store p address 0#usize ⦃phase=>post (.waiting phase address results)⦄) :
    prepareInvoke memory hooks floats allocator exec store platform address args results ⦃post⦄ := by
  apply prepare_invoke_checked_effects memory hooks floats allocator allocation exec store platform
    address function signature args results owner hf hs accepted owned post early
  intro prepared p owner frames values _ _ _
  exact handler prepared p owner frames values
end Exec.Interp.OpenCall
