import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
import Itasca.Runtime.SourceMachine.Core.Step
import Itasca.Runtime.SourceMachine.Numeric.Transition
import Itasca.Runtime.SourceMachine.StepSafety
import Itasca.Runtime.Interp.Control.StructuredPoint
import Itasca.Runtime.Interp.Control.NormalizeClosure

/-!
Code-size preservation is separate from value provenance and allowed syntax.

Main declarations: `FrameBoundClosure`. A direct consumer is `Interp.Machine.Control.BranchIfOwned`.
-/

namespace Itasca.Runtime.Interp

/-- Code-size preservation is separate from value provenance and allowed syntax. -/
def FrameBoundClosure (before after : SourceMachine.AFrame) : Prop :=
  ∀ bound, SourceMachine.FrameCodeBound bound before → SourceMachine.FrameCodeBound bound after

theorem FrameBoundClosure.refl (f : SourceMachine.AFrame) : FrameBoundClosure f f := fun _ h => h

theorem FrameBoundClosure.tail (f : SourceMachine.AFrame) (op : instr) (after : List instr)
    (locals values : List val) :
    FrameBoundClosure {f with code := op::after} {f with code := after,locals,vals := values} := by
  rintro bound ⟨size,labels⟩
  refine ⟨?_,labels⟩
  change sizeOf after ≤ bound
  simp only [List.cons.sizeOf_spec] at size
  omega

theorem FrameBoundClosure.replace (f : SourceMachine.AFrame) (op next : instr) (after : List instr)
    (locals values : List val) (smaller : sizeOf next ≤ sizeOf op) :
    FrameBoundClosure {f with code := op::after} {f with code := next::after,locals,vals := values} := by
  rintro bound ⟨size,labels⟩
  refine ⟨?_,labels⟩
  simp only [List.cons.sizeOf_spec] at size ⊢
  omega

theorem FrameBoundClosure.branch (f : SourceMachine.AFrame) (depth : Nat) (label : SourceMachine.Label)
    (lookup : f.labels[depth]? = some label) (values : List val) :
    FrameBoundClosure f {f with code := label.cont++label.after,labels := f.labels.drop (depth+1),vals := values} := by
  rintro bound ⟨size,labels⟩
  exact ⟨labels label (List.mem_of_getElem? lookup),fun next member => labels next (List.mem_of_mem_drop member)⟩

theorem FrameBoundClosure.state {before after} (closure : FrameBoundClosure before after)
    {bound s ambient rest} (bounded : SourceMachine.CodeBound bound ⟨s,ambient,before::rest,[]⟩) :
    SourceMachine.CodeBound bound ⟨s,ambient,after::rest,[]⟩ :=
  SourceMachine.bound_replace_frame bounded (closure bound (bounded.frames before (List.mem_cons_self ..)))

theorem ErasedSteps.code_bound {count before after} (steps : ErasedSteps count before after)
    {bound s ambient rest} (bounded : SourceMachine.CodeBound bound ⟨s,ambient,before::rest,[]⟩) :
    SourceMachine.CodeBound bound ⟨s,ambient,after::rest,[]⟩ := steps.closure.code_bound bounded
end Itasca.Runtime.Interp
