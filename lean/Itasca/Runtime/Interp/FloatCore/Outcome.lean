import Itasca.Runtime.Code.Local.Relations.Common.ScalarEmission
import Itasca.Runtime.Code.Local.Control.Common.Structured
import Itasca.Runtime.Code.Local.Control.Common.StructuredComposition
import Itasca.Runtime.Code.Local.Control.Common.StructuredLabels
import Itasca.Runtime.Interp.Control.StructuredPoint
import Itasca.Runtime.Abs.ModuleBindingsExtension
import Itasca.Runtime.Interp.Relations.SuspendedPoint
import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
import Itasca.Runtime.Interp.Machines.Slice.SliceExecution
import Itasca.Runtime.Abs.Core.Typing
import Itasca.Runtime.Abs.Float.Decode
import Itasca.Runtime.Abs.Ownership.Core
import Itasca.Runtime.Abs.Core
import Itasca.Runtime.Interp.Core.Mutation
import Itasca.Runtime.Interp.Relations.SourceCallCause
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Scalar Core traps are precise source failures, not arbitrary runtime errors. -/
def FloatCoreTrap (trap : runtime.Trap) : Prop :=
  trap = .Unreachable ∨ trap = .IntegerDivideByZero ∨ trap = .IntegerOverflow ∨ trap = .MemoryOutOfBounds ∨ trap = .InvalidConversionToInteger

variable {M P A : Type} {allocator : runtime.platform.Alloc A} {hooks : runtime.platform.Platform P M}
  {view : M → Slice U8} {code : Store.CodeInterpretation} {exec : runtime.interp.Execution}
  {store : runtime.store.Store M} {platform : P} {expected : List valtype}
  {codeLength pc : Nat} {pending : Bool} {source : Abs.AState}
  {out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P}

end Itasca.Runtime.Interp
