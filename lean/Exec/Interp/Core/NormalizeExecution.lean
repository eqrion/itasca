import Exec.Interp.Core.NormalizeClosure
import Exec.Interp.Core.OrdinaryExecution
import Exec.Spec.Extend
namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt Exec.Spec

theorem core_normalize_execution {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (index : Usize) (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (last : index.val+1 = exec.frames.length) (lookup : exec.frames.val[index.val]? = some raw)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (point : CoreFramePoint (Store.decodeStore view code store) raw f compiled C targets next output)
    (expected : List valtype)
    (machine : CoreExecution view code store exec ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ expected raw.pc.val false) :
    ∃ count g targets' next' output', ErasedSteps count f g ∧
      count + normalizationMeasure g ≤ normalizationMeasure f ∧
      FrameSlots exec raw g ∧ CoreFramePoint (Store.decodeStore view code store) raw g compiled C targets' next' output' ∧
      CoreExecution view code store exec ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ expected raw.pc.val false ∧
      FrameMetadata f g ∧
      (CoreForwardSkip (Store.decodeStore view code store) raw g compiled C targets' next' output' ∨ ReadySource g) := by
  obtain ⟨count,g,targets',next',output',chain,bound,represented,retained,typed,metadata,ready⟩ :=
    core_normalize exec raw compiled C targets next output (Store.decodeStore view code store) ambient f rest machine.typed slots point
  have same : exec.frames.set index raw = exec.frames := by
    apply alloc.vec.Vec.ext
    have valid : index.val < exec.frames.val.length := (List.getElem?_eq_some_iff.mp lookup).1
    have item : exec.frames.val[index.val]'valid = raw := (List.getElem?_eq_some_iff.mp lookup).2
    simp only [alloc.vec.Vec.set_val_eq]
    rw [←item,List.set_getElem_self]
  refine ⟨count,g,targets',next',output',chain,bound,represented,retained,?_,metadata,ready⟩
  exact machine.ordinary view code ambient f g rest expected raw.pc.val false (.refl store)
    (extend_store_refl _ machine.typed.typed.store) raw index raw.pc last lookup program (.ready retained)
    represented metadata (by simpa only [same]) (.refl _ _) typed (chain.core machine.core)
end Exec.Interp
