import Itasca.Runtime.Store.Initialization.InitializerErrors
import Itasca.Runtime.Store.Invariant.PrecommitError
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)
theorem eval_const_owned_errors (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (expr : Itasca.types.ConstExpr) (ty : Itasca.types.ValueType) (words : List U64)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hc : inst.module.functions.val[function.val]? = some code)
    (compiled : Compiler.InitializerCode code expr ty)
    (resolved : Interp.InitializerResolution store inst expr ty words)
    (bindings : InitializerBindings store inst) :
    runtime.interp.eval_const memory hooks floats allocator store platform instIndex function ty
      ⦃ out => out.2.1 = store ∧ out.2.2 = platform ∧
        (∀ value, out.1 = .Ok value → ValueInStore store value ∧ Interp.rawType value = ty) ∧
        ErrorAllowed ResourceError out.1 ⦄ := by
  obtain ⟨out, called, sameStore, sameHost, values⟩ := WP.spec_imp_exists
    (eval_const_owned memory hooks floats allocator law store platform instIndex function
      inst code expr ty words hi hc compiled resolved bindings)
  have errors := eval_const_errors memory hooks floats allocator law store platform instIndex function
    inst code expr ty words hi hc compiled resolved (initializer_reference_bound resolved bindings)
  rw [called] at errors
  simp only [WP.spec_ok] at errors
  refine WP.exists_imp_spec ⟨out, called, sameStore, sameHost, values, ?_⟩
  cases status : out.1 with
  | Ok value => trivial
  | Err error =>
    obtain ⟨resource, rfl⟩ := errors.2.2.2 error status
    trivial

end Itasca.Runtime.Store
