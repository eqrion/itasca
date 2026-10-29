import Itasca.Runtime.Interp.Relations.ReferenceTransfers
import Itasca.Runtime.Interp.Machine.Normalization
import Itasca.Runtime.Interp.Machine.Simulation.CoreErasure
import Itasca.Runtime.Interp.Relations.SourceClosure
import Itasca.Runtime.Interp.Control.NormalizeClosure
import Itasca.Runtime.Interp.Machine.Progress.OrdinaryExecution
import Itasca.Runtime.Interp.Machine.Coverage.SupportedControlSemantics
import Itasca.Runtime.Spec.Extend

/-!
Normalization of a structured source point and its execution relation. Closure over administrative choices yields the normalized machine certificate.
-/

/-! ## Normalize Closure -/

section

namespace Itasca.Runtime.Interp.Machine

theorem normalization_choice (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)] [ErasedHeads (emission compiled)] (C : context)
    (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (s : store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (typed : SourceMachine.CoreTyped ⟨s, ambient, f :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : FramePoint s raw f compiled C targets next output) :
    ForwardSkip s raw f compiled C targets next output ∨
      NormalizedPoint s exec raw compiled C f ∨ ReadySource f := by
  by_cases ready : ReadySource f
  · exact Or.inr (Or.inr ready)
  have frameTyped : SourceMachine.FrameTyped s f [] := by cases typed.typed.frames with | cons h _ => exact h
  cases code : f.code with
  | nil =>
    cases hlabels : f.labels with
    | nil => exact False.elim (ready (by simp [ReadySource, code, hlabels]))
    | cons label labels =>
      have same : { f with code := [], labels := label :: labels } = f := by rw [← code, ← hlabels]
      have choice := structured_label_normalizes exec raw compiled C targets next output
        s ambient f rest label labels (by simpa only [same] using typed.typed) slots (by simpa only [same] using point)
      simpa only [same] using choice.imp_right Or.inl
  | cons head after =>
    have same : { f with code := head :: after } = f := by rw [← code]
    cases head <;> try { solve | apply False.elim; apply ready; simp [ReadySource, code] }
    case NOP =>
      have choice := structured_nop_normalizes exec raw compiled C targets next output s f after
        slots (by simpa only [same] using point)
      simpa only [same] using choice.imp_right Or.inl
    case DROP =>
      have choice := structured_drop_normalizes exec raw compiled C targets next output s f after
        (by simpa only [same] using frameTyped) slots (by simpa only [same] using point)
      simpa only [same] using choice.imp_right Or.inl
    case BLOCK bt body =>
      have choice := structured_block_normalizes exec raw compiled C targets next output s ambient f rest bt body after
        (by simpa only [same] using typed.typed) slots (by simpa only [same] using point)
      simpa only [same] using choice.imp_right Or.inl

/-- Source-only normalization reaches either a retained forward jump or a
bytecode-bearing source position after a bounded finite number of reductions. -/
theorem normalize (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)] [ErasedHeads (emission compiled)] (C : context)
    (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (s : store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (typed : SourceMachine.CoreTyped ⟨s, ambient, f :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : FramePoint s raw f compiled C targets next output) :
    ∃ count g targets' next' output', ErasedSteps count f g ∧
      count + normalizationMeasure g ≤ normalizationMeasure f ∧
      FrameSlots exec raw g ∧
      FramePoint s raw g compiled C targets' next' output' ∧
      SourceMachine.CoreTyped ⟨s, ambient, g :: rest, []⟩ ∧ FrameMetadata f g ∧
      (ForwardSkip s raw g compiled C targets' next' output' ∨ ReadySource g) := by
  induction measure : normalizationMeasure f using Nat.strong_induction_on
      generalizing f targets next output with
  | h measure ih =>
    rcases normalization_choice exec raw compiled C targets next output s ambient f rest typed slots point with
      skip | ⟨g, targets', next', output', step, represented, continuation⟩ | ready
    · exact ⟨0, f, targets, next, output, .nil f, by omega, slots, point, typed,
        ⟨rfl, rfl, rfl, rfl⟩, Or.inl skip⟩
    · have nextTyped := (step.core_sound s ambient rest typed).1
      obtain ⟨count, final, labels, finish, results, steps, bound, represented, continuation, finalTyped, metadata, done⟩ :=
        ih (normalizationMeasure g) (by have := step.decreases; omega) targets' next' output' g nextTyped represented continuation rfl
      have chain := ErasedSteps.cons step steps
      exact ⟨count + 1, final, labels, finish, results, chain, by simpa only [measure] using chain.bound, represented, continuation,
        finalTyped, step.metadata.trans metadata, done⟩
    · exact ⟨0, f, targets, next, output, .nil f, by omega, slots, point, typed,
        ⟨rfl, rfl, rfl, rfl⟩, Or.inr ready⟩

end Itasca.Runtime.Interp.Machine

end

/-! ## Normalize Execution -/

section

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Spec

theorem normalize_execution {M : Type}
 (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (index : Usize) (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)] [ErasedHeads (emission compiled)] (C : context)
    (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (last : index.val+1 = exec.frames.length) (lookup : exec.frames.val[index.val]? = some raw)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view code store) raw f compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ expected raw.pc.val false) :
    ∃ count g targets' next' output', ErasedSteps count f g ∧
      count + normalizationMeasure g ≤ normalizationMeasure f ∧
      FrameSlots exec raw g ∧ FramePoint (Store.decodeStore view code store) raw g compiled C targets' next' output' ∧
      Execution view code store exec ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ expected raw.pc.val false ∧
      FrameMetadata f g ∧
      (ForwardSkip (Store.decodeStore view code store) raw g compiled C targets' next' output' ∨ ReadySource g) := by
  obtain ⟨count,g,targets',next',output',chain,bound,represented,retained,typed,metadata,ready⟩ :=
    normalize exec raw compiled C targets next output (Store.decodeStore view code store) ambient f rest machine.typed slots point
  have same : exec.frames.set index raw = exec.frames := by
    apply alloc.vec.Vec.ext
    have valid : index.val < exec.frames.val.length := (List.getElem?_eq_some_iff.mp lookup).1
    have item : exec.frames.val[index.val]'valid = raw := (List.getElem?_eq_some_iff.mp lookup).2
    simp only [alloc.vec.Vec.set_val_eq]
    rw [←item,List.set_getElem_self]
  refine ⟨count,g,targets',next',output',chain,bound,represented,retained,?_,metadata,ready⟩
  exact machine.ordinary view code ambient f g rest expected raw.pc.val false (.refl store)
    (extend_store_refl _ machine.typed.typed.store) raw index raw.pc last lookup program (.ready retained)
    represented metadata (by simpa only [same]) (.refl _ _) typed (Machine.erased_steps_supported chain machine.core)
end Itasca.Runtime.Interp.Machine

end
