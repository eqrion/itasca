import Itasca.Runtime.Store.Initialization.InitializerMetadata
import Itasca.Runtime.Store.Initialization.ElementTypes
import Itasca.Runtime.Store.Initialization.DataStagingLoop
import Itasca.Runtime.Store.Initialization.ElementContentEffect

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem DataStageEffect.contents {M : Type} {store after : runtime.store.Store M}
    {index inst} (effect : DataStageEffect store index inst after)
    (contents : ElementContents store) : ElementContents after := by
  cases effect with
  | unchanged => exact contents
  | appended datas addresses data stored mapped => simpa only [ElementContents, ReferenceShape] using contents

end Itasca.Runtime.Store
