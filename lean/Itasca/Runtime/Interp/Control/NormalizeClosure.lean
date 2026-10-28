import Itasca.Runtime.Interp.Relations.ReferenceTransfers
import Itasca.Runtime.Interp.Relations.Normalization
import Itasca.Runtime.Abs.Numeric.Decode
import Itasca.Runtime.Interp.Control.StructuredPoint
import Itasca.Runtime.Interp.Relations.ValueLookup
import Itasca.Runtime.Interp.Relations.SourceClosure

namespace Itasca.Runtime.Interp

/-- A source position that requires bytecode execution or function return. -/
def ReadySource (f : Abs.AFrame) : Prop :=
  match f.code with
  | [] => f.labels = []
  | .NOP :: _ | .DROP :: _ | .BLOCK _ _ :: _ => False
  | _ => True

theorem ErasedStep.metadata {before after} (step : ErasedStep before after) : FrameMetadata before after := by
  cases step <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem FrameMetadata.trans {before middle after}
    (first : FrameMetadata before middle) (second : FrameMetadata middle after) : FrameMetadata before after :=
  ⟨second.address.trans first.address, second.module.trans first.module,
    second.results.trans first.results, second.locals.trans first.locals⟩

theorem ErasedStep.closure {before after} (step : ErasedStep before after) : SourceClosure before after := by
  cases step with
  | nop f after => exact .tail _ _ _ _ _ (fun _ h => h)
  | drop f after front value => exact .tail { f with vals := front ++ [value] } .DROP after f.locals front (fun bound h => ⟨h.1, (Abs.valuesBound_append.mp h.2).1⟩)
  | block f bt body after front params results signature shape => exact .block _ _ _ _ _ _
  | label f label labels => exact .label _ _ _

theorem ErasedSteps.closure {count before after} (steps : ErasedSteps count before after) : SourceClosure before after := by
  induction steps with
  | nil => exact .refl _
  | cons step tail ih => exact step.closure.trans ih

end Itasca.Runtime.Interp
