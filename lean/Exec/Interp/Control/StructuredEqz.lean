import Exec.Interp.Relations.ReferenceTransfers
import Exec.Interp.Relations.SourceClosure
import Exec.Interp.Control.StructuredLinear
import Exec.Interp.Relations.ControlPoint
import Exec.Interp.Numeric.Integer.EqzCertified
import Exec.Interp.Relations.TypedOperands

namespace Exec.Interp
open Aeneas Aeneas.Std

theorem step_eqz_structured {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (functions : List functype) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (ty : Inn) (after : List instr)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := (.TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ)) :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : StructuredFramePoint raw { f with code := (.TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ)) :: after }
      compiled functions targets next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame) (targets' : List Code.LabelTarget) (next' : Nat)
        (output' : List valtype) (pending : Bool),
        { out.2.1 with slots := exec.slots } =
          { exec with frames := exec.frames.set index { raw with pc := pc } } ∧
        FrameSlots out.2.1 { raw with pc := pc } g ∧
        ControlPoint { raw with pc := pc } g compiled functions targets' next' output' pending ∧
        Abs.ATyped ⟨s, ambient, g :: rest, []⟩ ∧
        FrameMetadata f g ∧
        SourceClosure { f with code := (.TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ)) :: after } g ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending
          ⟨s, ambient, { f with code := (.TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ)) :: after } :: rest, []⟩
          ⟨s, ambient, g :: rest, []⟩ ⦄ := by
  have linear : linearSource (.TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ)) = true := by rfl
  rcases codeRel_linear_inv linear point.code.current with skip | branch
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    have targetPoint : StructuredFramePoint { raw with pc := target }
        { f with code := (.TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ)) :: after } compiled functions targets next output :=
      ⟨point.labels, ⟨continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩⟩
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
      index raw inst compiled target last hf hi hc pcBound fetched)
    intro out effect
    obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
    refine ⟨success, sameStore, samePlatform, target, { f with code := (.TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ)) :: after },
      targets, next, output, false, ?_, ?_, .ready targetPoint, typed, ⟨rfl, rfl, rfl, rfl⟩, .refl _, ?_⟩
    · rw [exactState]
    · rw [exactState]
      exact slots
    · exact Or.inl ⟨rfl, dispatchMeasure_forward _ _ _ _ forward continuation.entry_bound⟩
  · obtain ⟨middle, emitted, tail, head, fragment, continuation⟩ := branch
    obtain ⟨stack, slot, shape, emittedEq, middleEq, position⟩ := linearEmission_eqz_inv ty head
    have frameTyped : Abs.FrameTyped s { f with code := .TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ) :: after } [] := by
      cases typed.frames with | cons h _ => exact h
    obtain ⟨front, a, split, frontTypes, ha⟩ := frame_integer_suffix frameTyped stack ty shape
    have valuesSplit : f.vals = front ++ [Abs.integerVal ty a] := split
    have typed' : Abs.ATyped ⟨s, ambient,
        { f with code := .TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ) :: after, vals := front ++ [Abs.integerVal ty a] } :: rest, []⟩ := by
      simpa only [← valuesSplit] using typed
    have slots' : FrameSlots exec raw { f with vals := front ++ [Abs.integerVal ty a] } := by
      simpa only [← valuesSplit] using slots
    have slotPosition : slot.val = Code.slots ((f.locals ++ front).map Code.valueType) := by
      simpa only [List.map_append, Code.slots_append, frontTypes] using position
    have fetched : compiled.code.val[raw.pc.val]? = some (eqzInstruction ty slot) := by
      simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [emittedEq, List.getElem?_cons_zero])
    have endpoint : tail = raw.pc.val + 1 := by
      obtain ⟨_, _, _, _, h⟩ := fragment
      simpa only [emittedEq, List.length_singleton] using h
    have heights := frame_linear_heights frameTyped linear front (by
      rw [valuesSplit]
      simp [linearInputs])
    have labelsAfter : LabelsMatch (front ++ [Abs.integerVal .I32 (if a = 0 then 1 else 0)]) f.labels targets := by
      have labels : LabelsMatch (front ++ [Abs.integerVal ty a]) f.labels targets := by
        simpa only [← valuesSplit] using point.labels
      exact labels.replace_suffix heights
    have frameTyped' : Abs.FrameTyped s
        { f with code := .TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ) :: after, vals := front ++ [Abs.integerVal ty a] } [] := by
      simpa only [← valuesSplit] using frameTyped
    have nextFrame := Abs.integer_testop_frame_preservation (result := if a = 0 then 1 else 0)
      typed.store (by split <;> decide) frameTyped'
    have nextTyped := Abs.active_frame_preservation typed nextFrame rfl
    apply WP.spec_mono (step_eqz_refines memory hooks floats allocator exec store platform index raw inst compiled
      slot s ambient f rest after front ty a last hf hi hc fetched pcBound ha typed' slots' slotPosition)
    intro out effect
    obtain ⟨success, represented, sameStore, samePlatform, ⟨pc, hpc, unchanged⟩, simulation⟩ := effect
    have nextPoint : StructuredFramePoint { raw with pc := pc }
        { f with code := after, vals := front ++ [Abs.integerVal .I32 (if a = 0 then 1 else 0)] }
        compiled functions targets next output := by
      apply structured_linear_continuation point pc f.locals
        (front ++ [Abs.integerVal .I32 (if a = 0 then 1 else 0)]) after middle
      · simpa only [endpoint, hpc] using continuation
      · rfl
      · have valueType (ity : Inn) (n : Nat) : Code.valueType (Abs.integerVal ity n) = Code.integerType ity := by cases ity <;> rfl
        simp only [middleEq, List.map_append, List.map_cons, List.map_nil, valueType, Code.integerType, frontTypes]
      · exact labelsAfter
    refine ⟨success, sameStore, samePlatform, pc,
      { f with code := after, vals := front ++ [Abs.integerVal .I32 (if a = 0 then 1 else 0)] },
      targets, next, output, false, unchanged, represented, .ready nextPoint, nextTyped, ⟨rfl, rfl, rfl, rfl⟩, .tail _ _ _ _ _ (frame_references_numeric f front _ _ _ valuesSplit), ?_⟩
    apply ConcreteSim.of_source
    simpa only [← valuesSplit] using simulation

end Exec.Interp
