import Itasca.Runtime.Compiler.Local.Control.Function.CumulativeFunctionContext
import Itasca.Runtime.Compiler.Body.Relations.Executable.ExecutableEmission

/-!
Complete Wasm-profile function certificate, including typed SELECT, BR_TABLE and the actual function-local SIMD and target tables.

Main declarations: `ExecutableFunctionCode` and `DefinedExecutableFunctionCode`. A direct consumer is `Compiler.Body.Relations.Entry.ExecutableEntryCompilerFinish`.
-/

namespace Itasca.Runtime.Compiler

/-- Complete Wasm-profile function certificate, including typed SELECT,
BR_TABLE and the actual function-local SIMD and target tables. -/
abbrev ExecutableFunctionCode := IndexedFunctionCode ExecutableEmission
abbrev DefinedExecutableFunctionCode := DefinedIndexedFunctionCode ExecutableEmission
end Itasca.Runtime.Compiler
