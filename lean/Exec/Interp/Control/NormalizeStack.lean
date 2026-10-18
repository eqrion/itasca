import Exec.Interp.Relations.OrdinaryStack
import Exec.Interp.Control.NormalizeClosure

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Changing only the represented source position preserves the concrete stack
when normalization has retained the same live slots and function metadata. -/
theorem FrameStackRel.normalize {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {source updatedSource : Abs.AFrame} {rest : List Abs.AFrame}
    (relation : FrameStackRel store exec (source :: rest))
    (raw : runtime.interp.Frame) (index : Usize)
    (last : index.val + 1 = exec.frames.length)
    (lookup : exec.frames.val[index.val]? = some raw)
    (binding : FrameBinding store exec raw source)
    {compiled functions targets next output}
    (program : FrameProgram store raw compiled (source.locals.map Code.valueType) source.resultTypes functions)
    (point : StructuredFramePoint raw updatedSource compiled functions targets next output)
    (slots : FrameSlots exec raw updatedSource)
    (metadata : FrameMetadata source updatedSource) :
    FrameStackRel store exec (updatedSource :: rest) := by
  have bound : index.val < exec.frames.val.length := (List.getElem?_eq_some_iff.mp lookup).1
  have item : exec.frames.val[index.val]'bound = raw := (List.getElem?_eq_some_iff.mp lookup).2
  have same : exec.frames.set index raw = exec.frames := by
    apply alloc.vec.Vec.ext
    simp only [alloc.vec.Vec.set_val_eq]
    rw [← item, List.set_getElem_self]
  apply relation.ordinary raw index raw.pc last lookup binding program (.ready point) slots metadata
  · simpa only [same]
  · exact .refl _ _

theorem normalize_stack {M : Type} (store : runtime.store.Store M)
    (exec : runtime.interp.Execution) (raw : runtime.interp.Frame) (index : Usize)
    (compiled : runtime.bytecode.CompiledFunction) (functions : List functype)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (last : index.val + 1 = exec.frames.length)
    (lookup : exec.frames.val[index.val]? = some raw)
    (binding : FrameBinding store exec raw f)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes functions)
    (typed : Abs.ATyped ⟨s, ambient, f :: rest, []⟩)
    (slice : Abs.SliceState ⟨s, ambient, f :: rest, []⟩)
    (stack : FrameStackRel store exec (f :: rest))
    (slots : FrameSlots exec raw f)
    (point : StructuredFramePoint raw f compiled functions targets next output) :
    ∃ count g targets' next' output', ErasedSteps count f g ∧
      count + normalizationMeasure g ≤ normalizationMeasure f ∧
      FrameSlots exec raw g ∧
      StructuredFramePoint raw g compiled functions targets' next' output' ∧
      Abs.ATyped ⟨s, ambient, g :: rest, []⟩ ∧ Abs.SliceState ⟨s, ambient, g :: rest, []⟩ ∧
      FrameStackRel store exec (g :: rest) ∧ FrameMetadata f g ∧
      (ForwardSkip raw g compiled functions targets' next' output' ∨ ReadySource g) := by
  obtain ⟨count, g, targets', next', output', chain, bound, represented, continuation, nextTyped, nextSlice, metadata, done⟩ :=
    structured_normalize_slice exec raw compiled functions targets next output s ambient f rest typed slice slots point
  exact ⟨count, g, targets', next', output', chain, bound, represented, continuation,
    nextTyped, nextSlice, stack.normalize raw index last lookup binding program continuation represented metadata, metadata, done⟩

end Exec.Interp
