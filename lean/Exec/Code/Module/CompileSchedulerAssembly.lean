import Exec.Code.Module.CompileSourceCertificate
import Exec.Code.Module.CompileDriverFrame
import Exec.Code.Module.CompileSubmit
import Exec.Code.Module.CollectFunctions
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem sourceFunctions_length {raw : ModuleBinary.Module}
    (count : raw.functions.length = raw.codes.length) :
    (sourceFunctions raw).length = raw.functions.length := by
  simp [sourceFunctions, List.length_zipWith, count]

end Exec.Code
