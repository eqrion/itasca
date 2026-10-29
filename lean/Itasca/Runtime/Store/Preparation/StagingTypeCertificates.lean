import Itasca.Runtime.Store.Preparation.StagingTypeBindings
import Itasca.Runtime.Store.Initialization.InitializerMetadata
import Itasca.Runtime.Store.Initialization.ElementTypes
import Itasca.Runtime.Store.Initialization.ElementContentEffect
import Itasca.Runtime.Store.Initialization.DataLoopCertificates

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem storeParts_inj {M P : Type} (a b : runtime.store.Store M) (p q : P)
    (s t : core.result.Result Unit runtime.ExecError) :
    storeParts a p s = storeParts b q t ↔ a = b ∧ p = q ∧ s = t := by
  cases a; cases b
  simp [storeParts]

theorem storeStateParts_inj {M : Type} (a b : runtime.store.Store M)
    (s t : core.result.Result Unit runtime.ExecError) :
    storeStateParts a s = storeStateParts b t ↔ a = b ∧ s = t := by
  cases a; cases b
  simp [storeStateParts]

end Itasca.Runtime.Store
