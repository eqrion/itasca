import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Runtime.Compiler.Local.Control.Segments.Structured
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredComposition
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Interp.Control.StructuredPoint
import Itasca.Runtime.SourceMachine.ModuleBindingsExtension
import Itasca.Runtime.Interp.Relations.SuspendedPoint
import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
import Itasca.Runtime.Interp.Machine.Frames.Reposition
import Itasca.Runtime.SourceMachine.Core.Typing
import Itasca.Runtime.SourceMachine.Float.Descriptor
import Itasca.Runtime.SourceMachine.Ownership.Core
import Itasca.Runtime.SourceMachine.Core
import Itasca.Runtime.Interp.Machine.Mutation.Core
import Itasca.Runtime.Interp.Relations.SourceCallCause

/-!
Scalar Core traps are precise source failures, not arbitrary runtime errors.

Main declarations: `FloatCoreTrap`. A direct consumer is `Integration.Execution.Resources.Failure`.
-/

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
