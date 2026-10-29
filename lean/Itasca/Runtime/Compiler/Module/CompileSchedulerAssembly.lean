import Itasca.Runtime.Compiler.Module.CompileSourceCertificate
import Itasca.Runtime.Compiler.Module.CompileDriverFrame
import Itasca.Runtime.Compiler.Module.CompileSubmit
import Itasca.Runtime.Compiler.Module.CollectFunctions
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem sourceFunctions_length {raw : ModuleBinary.Module}
    (count : raw.functions.length = raw.codes.length) :
    (sourceFunctions raw).length = raw.functions.length := by
  simp [sourceFunctions, List.length_zipWith, count]

end Itasca.Runtime.Code
