import Itasca.Runtime.Interp.Relations.Arguments
import Itasca.Runtime.Interp.Relations.Fetch

/-! Public invocation rejection before execution begins. These conclusions
preserve execution state, store, platform, and the caller's result vector. -/
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

@[step] theorem func_type_lookup {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (store : runtime.store.Store M) (func : runtime.FuncAddr)
    (function : runtime.store.FuncInst) (signature : Itasca.types.FuncType)
    (owner : func.store = store.id)
    (hf : store.funcs.val[func.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature) :
    runtime.store.Store.func_type memory store func ⦃ out => out = .Ok signature ⦄ := by
  unfold runtime.store.Store.func_type
  simp only [runtime.store.Store.check, owner, ↓reduceIte, bind_ok,
    core.result.Result.Insts.CoreOpsTry.branch]
  step with vec_index_given store.funcs func.index function hf as ⟨found, hfound⟩
  subst found
  step with vec_index_given store.types function.signature signature hs as ⟨found, hfound⟩
  subst found
  rfl

variable {M P F A : Type}
  (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
  (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
  (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
  (func : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)

/-- Any error from the checked signature lookup is returned unchanged. -/
theorem invoke_signature_rejection (error : runtime.ExecError)
    (lookup : runtime.store.Store.func_type memory store func = .ok (.Err error)) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform func args results =
      .ok (.Err error, exec, store, platform, results) := by
  simp [runtime.interp.invoke_with, lookup, bind_ok,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from, lift, bind_ok]

/-- Foreign function handles reject before any index access or callback. -/
theorem invoke_wrong_store (foreign : func.store ≠ store.id) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform func args results =
      .ok (.Err .WrongStore, exec, store, platform, results) := by
  apply invoke_signature_rejection memory hooks floats allocator exec store platform func args results .WrongStore
  simp [runtime.store.Store.func_type, runtime.store.Store.check, foreign,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end Itasca.Runtime.Interp

