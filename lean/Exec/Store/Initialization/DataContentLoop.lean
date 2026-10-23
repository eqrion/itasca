import Exec.Store.Initialization.InitializerMetadata
import Exec.Store.Initialization.ElementTypes
import Exec.Store.Initialization.DataStagingLoop
import Exec.Store.Initialization.ElementContentEffect

namespace Exec.Store
open Aeneas Aeneas.Std

theorem DataStageEffect.contents {M : Type} {store after : runtime.store.Store M}
    {index inst} (effect : DataStageEffect store index inst after)
    (contents : ElementContents store) : ElementContents after := by
  cases effect with
  | unchanged => exact contents
  | appended datas addresses data stored mapped => simpa only [ElementContents, ReferenceShape] using contents

end Exec.Store
