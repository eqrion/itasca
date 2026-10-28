import Exec.Code.Local.Control.Common.IndexedFunction
import Exec.Code.Body.Relations.Common.ExecutableEmission
namespace Itasca.Runtime.Code

/-- Complete Wasm-profile function certificate, including typed SELECT,
BR_TABLE and the actual function-local SIMD and target tables. -/
abbrev ExecutableFunctionCode := IndexedFunctionCode ExecutableEmission
abbrev DefinedExecutableFunctionCode := DefinedIndexedFunctionCode ExecutableEmission
end Itasca.Runtime.Code
