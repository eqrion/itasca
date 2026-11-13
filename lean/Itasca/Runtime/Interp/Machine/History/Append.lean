import Itasca.Runtime.Interp.Relations.ReferenceTransfers
import Itasca.Runtime.Interp.Relations.SourceClosure
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.Interp.Relations.ControlPoint
import Itasca.Runtime.Interp.Numeric.Integer.NumericFetch
import Itasca.Runtime.Interp.Numeric.Integer.IntCounts
import Itasca.Runtime.SourceMachine.Numeric.TransitionSimulation
import Itasca.Runtime.Interp.Machine.Frames.Reposition
import Itasca.Runtime.Interp.Control.NormalizeCompose
import Itasca.Runtime.Interp.Relations.PrefixDispatch
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredComposition
import Itasca.Runtime.Interp.Control.BrTableSource
import Itasca.Runtime.Interp.Relations.SourceCallCause
import Itasca.Runtime.Interp.Machine.Emission.Local
import Itasca.Runtime.Interp.Relations.Fetch
import Itasca.Runtime.SourceMachine.Numeric.Decode
import Itasca.Runtime.Interp.Relations.TypedOperands
import Itasca.Runtime.Interp.Relations.Rel
import Itasca.Runtime.SourceMachine.Sim.Structured
import Itasca.Runtime.Interp.Relations.ConstCodePoint
import Itasca.Runtime.Interp.Relations.LocalCodePoint
import Itasca.Runtime.Interp.Relations.ValueLookup
import Itasca.Runtime.Interp.Relations.ControlEntry
import Itasca.Runtime.Interp.Relations.Capacity
import Itasca.Runtime.Interp.Relations.LocalCapacity
import Itasca.Runtime.Interp.Relations.Normalization
import Itasca.Runtime.SourceMachine.Numeric.Transition
import Itasca.Runtime.SourceMachine.BrTable
import Itasca.Runtime.Interp.Relations.CompiledFunctions
import Itasca.Runtime.Compiler.Local.Relations.Function.Function
import Itasca.Runtime.Interp.Calls.IndirectResolve
import Itasca.Runtime.SourceMachine.Bound
import Itasca.Runtime.Interp.Calls.ReturnRefinement
import Itasca.Runtime.Interp.Relations.StackRelation
import Itasca.Runtime.Interp.Control.LabelCompletion
import Itasca.Runtime.Interp.Relations.Epilogue
import Itasca.Runtime.Interp.Relations.HeadCoverage
import Itasca.Runtime.Interp.Machine.Simulation.CoreErasure
import Itasca.Runtime.Interp.Relations.ExecutionLoop

/-!
Appending execution history while retaining its recorded source trace.

Main declarations: `history_append`. A direct consumer is `Interp.Machine.Progress.ActiveLoop`.
-/

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
