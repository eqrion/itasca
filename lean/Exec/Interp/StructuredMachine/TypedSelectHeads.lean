import Exec.Interp.StructuredMachine.FloatHeads
import Exec.Code.Local.Source.TypedSelectEmission

namespace Exec.Interp.StructuredMachine

class TypedSelectHeads (family : ContextEmission) : Prop where
  project : ∀ {C stack ty emitted output}, family C stack (.SELECT (some [ty])) emitted output →
    Code.TypedSelectEmission C stack (.SELECT (some [ty])) emitted output

end Exec.Interp.StructuredMachine
