import Aeneas
import Itasca.Results.Definitions
import Itasca.Results.Validate
import Itasca.Results.Stream
import Itasca.Results.Batch
import Itasca.Results.Trace
import Itasca.Results.Unique
import Itasca.Results.Compile
import Itasca.Results.Instantiate
import Itasca.Results.Invoke
import Itasca.Results.Store
import Itasca.Runtime.Platform.VecMemory
import Itasca.Runtime.Platform.FloatWitness
import Itasca.Runtime.Integration.Host.TrapWitness
import Itasca.Spec.Typing

/-!
# Itasca public interface

The [Results guide](Itasca/Results/README.md) indexes the validation,
compilation, and execution guarantees. The
[public definitions](Itasca/Results/Definitions/README.md) describe their
premises, certificates, and embedder obligations.
-/
