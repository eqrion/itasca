import Itasca.Runtime.Interp.Relations.ReferenceTransfers
import Itasca.Runtime.Interp.Relations.SourceClosure
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.Interp.Relations.ControlPoint
import Itasca.Runtime.Interp.Numeric.Integer.NumericFetch
import Itasca.Runtime.Interp.Numeric.Integer.NumericCodePoint
import Itasca.Runtime.Abs.Numeric.TransitionSimulation
import Itasca.Runtime.Interp.Machines.Slice.SliceExecution
import Itasca.Runtime.Interp.Control.NormalizeCompose
import Itasca.Runtime.Interp.Relations.PrefixDispatch
import Itasca.Runtime.Code.Local.Control.Common.StructuredComposition
import Itasca.Runtime.Interp.Control.StructuredPoint
import Itasca.Runtime.Interp.Control.SkipStack
import Itasca.Runtime.Interp.Relations.SourceCallCause
import Itasca.Runtime.Interp.Machines.Slice.SliceOpcode
import Itasca.Runtime.Interp.Machines.Slice.SliceBinary
import Itasca.Runtime.Interp.Relations.Fetch
import Itasca.Runtime.Abs.Numeric.Decode
import Itasca.Runtime.Interp.Relations.TypedOperands
import Itasca.Runtime.Interp.Relations.Rel
import Itasca.Runtime.Abs.Sim.Typed
import Itasca.Runtime.Interp.Relations.ConstCodePoint
import Itasca.Runtime.Interp.Relations.LocalCodePoint
import Itasca.Runtime.Interp.Relations.ValueLookup
import Itasca.Runtime.Interp.Control.BranchNoCopy
import Itasca.Runtime.Interp.Control.BranchConditionStep
import Itasca.Runtime.Interp.Relations.ControlEntry
import Itasca.Runtime.Interp.Relations.Capacity
import Itasca.Runtime.Interp.Relations.LocalCapacity
import Itasca.Runtime.Interp.Control.LoopHead
import Itasca.Runtime.Interp.Relations.Normalization
import Itasca.Runtime.Abs.Numeric.Transition
import Itasca.Runtime.Abs.ReferenceBounds
import Itasca.Runtime.Interp.Relations.CompiledFunctions
import Itasca.Runtime.Code.Local.Relations.Common.Function
import Itasca.Runtime.Interp.Calls.CallRefinement
import Itasca.Runtime.Interp.Calls.CallStack
import Itasca.Runtime.Abs.Numeric.Effect
import Itasca.Runtime.Abs.StepSafety
import Itasca.Runtime.Abs.Results
import Itasca.Runtime.Interp.Calls.ReturnResult
import Itasca.Runtime.Interp.Calls.ReturnRefinement
import Itasca.Runtime.Interp.Relations.StackRelation
import Itasca.Runtime.Interp.Control.LabelCompletion
import Itasca.Runtime.Interp.Relations.Epilogue
import Itasca.Runtime.Interp.Control.StructuredUnreachable
import Itasca.Runtime.Interp.Relations.HeadCoverage
import Itasca.Runtime.Interp.Control.NormalizeClosure
import Itasca.Runtime.Interp.Machines.Slice.SliceMeasure
import Itasca.Runtime.Interp.Relations.ExecutionLoop

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem history_append {S : Type} {next : S → List SpecExt.HostEvent → S → Prop}
    {n m : Nat} {first middle last : S} {events rest : List SpecExt.HostEvent}
    (left : Spec.Iterations next n first events middle) (right : Spec.Iterations next m middle rest last) :
    Spec.Iterations next (n + m) first (events ++ rest) last := by
  induction left with
  | refl _ => simpa using right
  | cons step _ ih => simpa [Nat.add_assoc, Nat.add_comm, List.append_assoc] using Spec.Iterations.cons step (ih right)

end Itasca.Runtime.Interp
