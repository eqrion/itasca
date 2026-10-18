import Exec.Interp.Relations.Arguments
import Exec.Interp.Relations.Fetch

/-! Public invocation rejection before execution begins. These conclusions
preserve execution state, store, platform, and the caller's result vector. -/
namespace Exec.Interp
open Aeneas Aeneas.Std

@[step] theorem func_type_lookup {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (store : runtime.store.Store M) (func : runtime.FuncAddr)
    (function : runtime.store.Function) (signature : Itasca.types.FuncType)
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

/-- Argument rejection depends only on length, scalar tags, and reference
store identities. It occurs before interrupt hooks or allocation. -/
theorem invoke_argument_rejection (signature : Itasca.types.FuncType)
    (error : runtime.ExecError)
    (lookup : runtime.store.Store.func_type memory store func = .ok (.Ok signature))
    (rejected : (if args.length = signature.params.length then
      checkArguments store.id args.val signature.params.val else .Err .BadArguments) = .Err error) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform func args results =
      .ok (.Err error, exec, store, platform, results) := by
  obtain ⟨out, hcheck, hout⟩ := WP.spec_imp_exists
    (check_values_effect memory store args (alloc.vec.Vec.deref signature.params))
  have hdecision : out = (if args.length = signature.params.length then
      checkArguments store.id args.val signature.params.val else .Err .BadArguments) := by
    simpa [alloc.vec.Vec.deref] using hout
  have ho : out = .Err error := hdecision.trans rejected
  rw [ho] at hcheck
  simp [runtime.interp.invoke_with, lookup, hcheck, bind_ok,
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

/-- For an issued function/signature lookup, an argument-count mismatch
returns BadArguments and preserves all caller-visible state. -/
theorem invoke_argument_count (function : runtime.store.Function)
    (signature : Itasca.types.FuncType) (owner : func.store = store.id)
    (hf : store.funcs.val[func.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (mismatch : args.length ≠ signature.params.length) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform func args results =
      .ok (.Err .BadArguments, exec, store, platform, results) := by
  obtain ⟨answer, lookup, ha⟩ := WP.spec_imp_exists
    (func_type_lookup memory store func function signature owner hf hs)
  rw [ha] at lookup
  apply invoke_argument_rejection memory hooks floats allocator exec store platform func args results
    signature .BadArguments lookup
  simp [mismatch]

end Exec.Interp

