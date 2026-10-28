import Exec.Store.Initialization.InitializerMetadata
import Exec.Store.Api.GlobalEffects

/-! The actual staged global loop preserves pre-existing store objects and the
linked initializer context through all allocation/refusal branches. -/
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

def InitializerContext {M : Type} (store : runtime.store.Store M) (index : Usize)
    (module : runtime.compiler.ExecutableModule) : Prop :=
  ∃ inst, store.instances.val[index.val]? = some inst ∧ inst.module = module ∧
    InitializerBindings store inst ∧ InitializerImports store inst ∧ InitializerSegmentBindings store inst

end Itasca.Runtime.Store
