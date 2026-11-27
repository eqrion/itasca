import WebAssembly.Binary.Unique
import Itasca.Binary.ModuleSource
import Itasca.Binary.SourceInjective

/-!
# Decoding uniqueness

A byte string encodes at most one raw module. Custom section placement and omitted empty sections
introduce no ambiguity. Neither typing nor implementation limits are premises, so a module that
`metadata.validate_module` accepts has exactly one decoding.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- A complete module has one decoding under the WebAssembly Core 2.0 grammar. -/
theorem Binary.module_unique {x y : Binary.Module}
    {bytes : List U8}
    (left_encoding : Binary.ModuleEncodingWith (CodeEntry.CodeEncoding) x bytes)
    (right_encoding : Binary.ModuleEncodingWith (CodeEntry.CodeEncoding) y bytes) : x = y :=
  Binary.Source.rawModuleInjective (WebAssembly.Binary.ModuleEncoding.unique
    (Binary.Source.moduleEncoding left_encoding) (Binary.Source.moduleEncoding right_encoding))

end Itasca
