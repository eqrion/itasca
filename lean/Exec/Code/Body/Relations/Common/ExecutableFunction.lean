import Exec.Code.Local.Control.Common.IndexedFunction
import Exec.Code.Body.Relations.Common.ExecutableEmission
namespace Exec.Code

/-- Complete Wasm-profile function certificate, including typed SELECT,
BR_TABLE and the actual function-local SIMD and target tables. -/
abbrev ExecutableFunctionCode := IndexedFunctionCode ExecutableEmission
abbrev DefinedExecutableFunctionCode := DefinedIndexedFunctionCode ExecutableEmission
end Exec.Code
