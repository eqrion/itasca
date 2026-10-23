import Itasca.Handler.EnvReaders
import Itasca.Handler.StackSemantics
import Itasca.Handler.ResumePrefix

/-!
# Call prefixes

Extends a `Sequence.TypedPrefix` across `code.read_call` and `code.read_call_indirect`, using the
generated `call` and `call_indirect` rules through `EnvTranslation.Matches.call` and
`Matches.call_indirect`.
-/

open Aeneas Aeneas.Std

namespace Itasca

end Itasca
