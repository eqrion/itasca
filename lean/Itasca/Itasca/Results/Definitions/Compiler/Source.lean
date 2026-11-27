import Aeneas
import ItascaRust.Funs
import ItascaRust.Types
import Itasca.Results.Definitions.Binary
import Itasca.Results.Definitions.Foundations
import Itasca.Results.Definitions.Representation
import Itasca.Results.Definitions.Validation
import WebAssembly

/-!
# Source function interpretation

Raw function declarations and bodies determine the source code installed by
instantiation. This interpretation is independent of compilation budgets and
emission certificates. Target instructions, control layouts and initializer
accounting belong to Runtime/Compiler.

-/

section CompilerSourceFunctions

namespace Itasca.Compiler

open Aeneas Aeneas.Std Itasca

/-- The store's code constructor for one independently decoded function. -/
def sourceFunctionCode (index : U32) (entry : Binary.Code) : funccode :=
  .FUNC (.mk_uN index.val) (entry.declared.map (fun ty => .LOCAL (Translation.valueType ty))) entry.body

def sourceFunctions (raw : Binary.Module) : List funccode :=
  List.zipWith sourceFunctionCode raw.functions raw.codes

end Itasca.Compiler

end CompilerSourceFunctions
