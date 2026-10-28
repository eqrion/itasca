import Exec.Interp.Relations.FrameStoreMetadata
import Exec.Abs.Core.Step
import Exec.Abs.Numeric.Effect
import Exec.Abs.StepSafety
import Exec.Interp.Control.StructuredPoint
import Exec.Interp.Control.NormalizeClosure
namespace Itasca.Runtime.Interp

/-- Code-size preservation is separate from value provenance and allowed syntax. -/
def FrameBoundClosure (before after : Abs.AFrame) : Prop :=
  ∀ bound, Abs.FrameCodeBound bound before → Abs.FrameCodeBound bound after

theorem FrameBoundClosure.refl (f : Abs.AFrame) : FrameBoundClosure f f := fun _ h => h

theorem FrameBoundClosure.tail (f : Abs.AFrame) (op : instr) (after : List instr)
    (locals values : List val) :
    FrameBoundClosure {f with code := op::after} {f with code := after,locals,vals := values} := by
  rintro bound ⟨size,labels⟩
  refine ⟨?_,labels⟩
  change sizeOf after ≤ bound
  simp only [List.cons.sizeOf_spec] at size
  omega

theorem FrameBoundClosure.replace (f : Abs.AFrame) (op next : instr) (after : List instr)
    (locals values : List val) (smaller : sizeOf next ≤ sizeOf op) :
    FrameBoundClosure {f with code := op::after} {f with code := next::after,locals,vals := values} := by
  rintro bound ⟨size,labels⟩
  refine ⟨?_,labels⟩
  simp only [List.cons.sizeOf_spec] at size ⊢
  omega

theorem FrameBoundClosure.branch (f : Abs.AFrame) (depth : Nat) (label : Abs.Label)
    (lookup : f.labels[depth]? = some label) (values : List val) :
    FrameBoundClosure f {f with code := label.cont++label.after,labels := f.labels.drop (depth+1),vals := values} := by
  rintro bound ⟨size,labels⟩
  exact ⟨labels label (List.mem_of_getElem? lookup),fun next member => labels next (List.mem_of_mem_drop member)⟩

theorem FrameBoundClosure.state {before after} (closure : FrameBoundClosure before after)
    {bound s ambient rest} (bounded : Abs.CodeBound bound ⟨s,ambient,before::rest,[]⟩) :
    Abs.CodeBound bound ⟨s,ambient,after::rest,[]⟩ :=
  Abs.bound_replace_frame bounded (closure bound (bounded.frames before (List.mem_cons_self ..)))

theorem ErasedSteps.codeBound {count before after} (steps : ErasedSteps count before after)
    {bound s ambient rest} (bounded : Abs.CodeBound bound ⟨s,ambient,before::rest,[]⟩) :
    Abs.CodeBound bound ⟨s,ambient,after::rest,[]⟩ := steps.closure.codeBound bounded
end Itasca.Runtime.Interp
