import Exec.Interp.Relations.ReferenceTransfers
import Exec.Interp.Relations.SourceClosure
import Exec.Interp.Control.StructuredLinear
import Exec.Interp.Relations.ControlPoint
import Exec.Interp.Numeric.Integer.NumericFetch
import Exec.Interp.Numeric.Integer.NumericCodePoint
import Exec.Abs.Numeric.TransitionSimulation
import Exec.Interp.Machines.Slice.SliceExecution
import Exec.Interp.Control.NormalizeCompose
import Exec.Interp.Relations.PrefixDispatch
import Exec.Code.Local.Control.Common.StructuredComposition
import Exec.Interp.Control.StructuredPoint
import Exec.Interp.Control.SkipStack
import Exec.Interp.Relations.SourceCallCause
import Exec.Interp.Machines.Slice.SliceOpcode
import Exec.Interp.Machines.Slice.SliceBinary
import Exec.Interp.Relations.Fetch
import Exec.Abs.Numeric.Decode
import Exec.Interp.Relations.TypedOperands
import Exec.Interp.Relations.Rel
import Exec.Abs.Sim.Typed
import Exec.Interp.Relations.ConstCodePoint
import Exec.Interp.Relations.LocalCodePoint
import Exec.Interp.Relations.ValueLookup
import Exec.Interp.Control.BranchNoCopy
import Exec.Interp.Control.BranchConditionStep
import Exec.Interp.Relations.ControlEntry
import Exec.Interp.Relations.Capacity
import Exec.Interp.Relations.LocalCapacity
import Exec.Interp.Control.LoopHead
import Exec.Interp.Relations.Normalization
import Exec.Abs.Numeric.Transition
import Exec.Abs.ReferenceBounds
import Exec.Interp.Relations.CompiledFunctions
import Exec.Code.Local.Relations.Common.Function
import Exec.Interp.Calls.CallRefinement
import Exec.Interp.Calls.CallStack
import Exec.Abs.Numeric.Effect
import Exec.Abs.StepSafety
import Exec.Abs.Results
import Exec.Interp.Calls.ReturnResult
import Exec.Interp.Calls.ReturnRefinement
import Exec.Interp.Relations.StackRelation
import Exec.Interp.Control.LabelCompletion
import Exec.Interp.Relations.Epilogue
import Exec.Interp.Control.StructuredUnreachable
import Exec.Interp.Relations.HeadCoverage
import Exec.Interp.Control.NormalizeClosure
import Exec.Interp.Machines.Slice.SliceMeasure
import Exec.Interp.Relations.ExecutionLoop

namespace Exec.Interp
open Aeneas Aeneas.Std

theorem history_append {S : Type} {next : S → List SpecExt.HostEvent → S → Prop}
    {n m : Nat} {first middle last : S} {events rest : List SpecExt.HostEvent}
    (left : Spec.Iterations next n first events middle) (right : Spec.Iterations next m middle rest last) :
    Spec.Iterations next (n + m) first (events ++ rest) last := by
  induction left with
  | refl _ => simpa using right
  | cons step _ ih => simpa [Nat.add_assoc, Nat.add_comm, List.append_assoc] using Spec.Iterations.cons step (ih right)

end Exec.Interp
