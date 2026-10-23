import Exec.Interp.Relations.SourceClosure
import Exec.Interp.Core.ControlInversion
import Exec.Interp.Core.SuspendedPoint
import Exec.Abs.Core.Typing
import Exec.Abs.Core.Step
import Exec.Interp.Relations.ControlEntry
import Exec.Interp.Relations.ControlPoint
import Exec.Interp.Control.LoopHead

namespace Exec.Interp
open Aeneas Aeneas.Std

theorem step_loop_core {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (bt : blocktype) (body after : List instr)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (typed : Abs.CoreTyped ⟨s, ambient, { f with code := .LOOP bt body :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : CoreFramePoint s raw { f with code := .LOOP bt body :: after }
      compiled C targets next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧
      ((out.1 = .Ok () ∧
      ∃ (pc : U32) (g : Abs.AFrame) (targets' : List Code.LabelTarget) (next' : Nat)
        (output' : List valtype) (pending : Bool),
        { out.2.1 with slots := exec.slots } =
          { exec with frames := exec.frames.set index { raw with pc := pc } } ∧
        FrameSlots out.2.1 { raw with pc := pc } g ∧
        CoreControlPoint s { raw with pc := pc } g compiled C targets' next' output' pending ∧
        Abs.CoreTyped ⟨s, ambient, g :: rest, []⟩ ∧
        FrameMetadata f g ∧
        SourceClosure { f with code := .LOOP bt body :: after } g ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending
          ⟨s, ambient, { f with code := .LOOP bt body :: after } :: rest, []⟩
          ⟨s, ambient, g :: rest, []⟩ ∧
        (g = {f with code := .LOOP bt body :: after} ∨ Abs.Core.step ⟨s,ambient,{f with code := .LOOP bt body :: after}::rest,[]⟩ = .next ⟨s,ambient,g::rest,[]⟩)) ∨
      (out.1 = .Err .Terminated ∧ hooks.interrupt platform = .ok (.Terminate, out.2.2.2))) ⦄ := by
  rcases coreCodeRel_loop_inv point.code.current with skip | branch
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    have targetPoint : CoreFramePoint s { raw with pc := target }
        { f with code := .LOOP bt body :: after } compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels, ⟨continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩⟩
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
      index raw inst compiled target last hf hi hc pcBound fetched)
    intro out effect
    obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
    refine ⟨sameStore, Or.inl ⟨success, target, { f with code := .LOOP bt body :: after },
      targets, next, output, false, ?_, ?_, .ready targetPoint, typed, ⟨rfl, rfl, rfl, rfl⟩, .refl _, ?_,Or.inl rfl⟩⟩
    · rw [exactState]
    · rw [exactState]
      exact slots
    · exact Or.inl ⟨rfl, dispatchMeasure_forward _ _ _ _ forward continuation.entry_bound⟩
  · obtain ⟨front, params, results, entry, exit, normalLive, shape, atEntry, signature, head, bodyCode, continuation, bounds⟩ := branch
    have sourceStep := loop_source_step s ambient f rest bt body after front params results (by simpa only [point.bindings.types] using signature) shape
    have typedNext := Abs.loop_preservation s ambient f rest after bt body _ typed.typed sourceStep
    have simulation := Abs.typed_loop_simulation s ambient f rest after bt body _ typed.typed sourceStep
    apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
      .LoopHead last hf hi hc (by simpa only [atEntry] using head) pcBound
    intro pc hpc
    apply WP.spec_mono (dispatch_loopHead_effect memory hooks floats allocator law
      { exec with frames := exec.frames.set index { raw with pc := pc } } store platform index raw)
    intro out effect
    obtain ⟨exactState, sameStore, decision, hook, result⟩ := effect
    refine ⟨sameStore, ?_⟩
    cases decision with
    | Terminate => exact Or.inr ⟨result, hook⟩
    | Continue =>
      refine Or.inl ⟨result, pc,
        { f with code := body, labels := ⟨params, results, [.LOOP bt body], front.length, after⟩ :: f.labels },
        ⟨front, params, results, entry, exit, [.LOOP bt body], after, normalLive, true⟩ :: targets,
        exit, front ++ results, false, ?_, ?_, .ready ?_, ⟨typedNext,typed.contents⟩, ⟨rfl, rfl, rfl, rfl⟩, .loop _ _ _ _ _ _ _, ?_,Or.inr sourceStep⟩
      · rw [exactState]
      · rw [exactState]
        exact slots
      · refine ⟨point.bindings,point.locals,point.labels.enter front params results params entry exit [.LOOP bt body] after shape, ?_⟩
        simpa only [shape, hpc, atEntry] using Code.StructuredCode.Point.loop_body signature head bodyCode continuation bounds
          point.code.targets point.code.normal point.code.exit point.code.root
      · apply ConcreteSim.of_source
        exact simulation

end Exec.Interp
