import Exec.Interp.Relations.ReferenceTransfers
import Exec.Interp.Relations.SourceClosure
import Exec.Interp.Control.StructuredLinear
import Exec.Interp.Relations.ControlPoint
import Exec.Interp.Numeric.Integer.NumericFetch
import Exec.Interp.Numeric.Integer.NumericCodePoint
import Exec.Abs.Numeric.TransitionSimulation

namespace Exec.Interp
open Aeneas Aeneas.Std Abs.Numeric

theorem step_numeric_structured {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (functions : List functype) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (op : Instruction) (after : List instr)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : StructuredFramePoint raw { f with code := op.source :: after }
      compiled functions targets next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ((out.1 = .Ok () ∧
      ∃ (pc : U32) (g : Abs.AFrame),
        { out.2.1 with slots := exec.slots } =
          { exec with frames := exec.frames.set index { raw with pc := pc } } ∧
        FrameSlots out.2.1 { raw with pc := pc } g ∧
        StructuredFramePoint { raw with pc := pc } g compiled functions targets next output ∧
        Abs.ATyped ⟨s, ambient, g :: rest, []⟩ ∧
        FrameMetadata f g ∧
        SourceClosure { f with code := op.source :: after } g ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false
          ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩
          ⟨s, ambient, g :: rest, []⟩) ∨
      (∃ trap, out.1 = .Err (.Trap trap) ∧
        (trap = .IntegerDivideByZero ∨ trap = .IntegerOverflow) ∧
        ∃ count, 0 < count ∧ Spec.StepsHN count
          (Abs.decode ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩) []
          ⟨⟨s, ambient⟩, [.TRAP]⟩)) ⦄ := by
  have linear : linearSource op.source = true := by
    cases op <;> (try casesm* Conversion) <;> rfl
  rcases codeRel_linear_inv linear point.code.current with skip | branch
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    have targetPoint : StructuredFramePoint { raw with pc := target }
        { f with code := op.source :: after } compiled functions targets next output :=
      ⟨point.labels, ⟨continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩⟩
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
      index raw inst compiled target last hf hi hc pcBound fetched)
    intro out effect
    obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
    refine ⟨sameStore, samePlatform, .inl ⟨success, target, { f with code := op.source :: after },
      ?_, ?_, targetPoint, typed, ⟨rfl, rfl, rfl, rfl⟩, .refl _, ?_⟩⟩
    · rw [exactState]
    · rw [exactState]
      exact slots
    · exact Or.inl ⟨rfl, dispatchMeasure_forward _ _ _ _ forward continuation.entry_bound⟩
  · obtain ⟨middle, emitted, tail, head, fragment, continuation⟩ := branch
    obtain ⟨stack, left, right, shape, emittedEq, middleEq, leftPos, rightPos⟩ := linearEmission_numeric_inv op head
    have frameTyped : Abs.FrameTyped s { f with code := op.source :: after } [] := by
      cases typed.frames with | cons h _ => exact h
    obtain ⟨front, a, b, split, wfFront, heights⟩ := op.typed_operands_bounds frameTyped
    have frontTypes : front.map Code.valueType = stack := by
      rw [split, List.map_append, numericOperand_types] at shape
      exact List.append_cancel_right shape
    have leftPosition : left.val = Code.slots ((f.locals ++ front).map Code.valueType) := by
      simpa only [List.map_append, Code.slots_append, frontTypes] using leftPos
    have fetched : compiled.code.val[raw.pc.val]? = some (Code.integerInstruction op left left right) := by
      simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [emittedEq, List.getElem?_cons_zero])
    have endpoint : tail = raw.pc.val + 1 := by
      obtain ⟨_, _, _, _, h⟩ := fragment
      simpa only [emittedEq, List.length_singleton] using h
    have represented : ValuesAt exec.slots.val raw.base.val ((f.locals ++ front) ++ op.operands a b) := by
      simpa only [FrameSlots, split, List.append_assoc] using slots
    apply WP.spec_mono (step_integer_values memory hooks floats allocator exec store platform index raw inst compiled
      op left right (f.locals ++ front) a b last hf hi hc fetched pcBound represented leftPosition rightPos)
    intro out effect
    obtain ⟨sameStore, samePlatform, pc, pcEq, effect⟩ := effect
    refine ⟨sameStore, samePlatform, ?_⟩
    cases operation : op.apply a b with
    | none =>
      simp only [NumericValuesEffect, operation] at effect
      obtain ⟨trap, kind, exactEffect⟩ := effect
      have sourceTrap : Abs.astep ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩ = .trap := by
        have h := astep_operands ⟨s, ambient, [], []⟩ f rest after front op a b
        simp only [finish, operation] at h
        simpa only [← split] using h
      refine .inr ⟨trap, congrArg Prod.fst exactEffect, kind, ?_⟩
      exact astep_trap_simulation s ambient f rest after op typed sourceTrap
    | some value =>
      simp only [NumericValuesEffect, operation] at effect
      obtain ⟨success, represented, unchanged⟩ := effect
      have sourceStep : Abs.astep ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩ = .next
          ⟨s, ambient, { f with code := after, vals := front ++ [Abs.integerVal op.output value.toNat] } :: rest, []⟩ := by
        have h := astep_operands ⟨s, ambient, [], []⟩ f rest after front op a b
        simp only [finish, operation, Abs.advance] at h
        simpa only [← split] using h
      have nextTyped := Abs.instruction_preservation s ambient f rest _ after _ (.numeric op) typed sourceStep
      have nextPoint : StructuredFramePoint { raw with pc := pc }
          { f with code := after, vals := front ++ [Abs.integerVal op.output value.toNat] }
          compiled functions targets next output := by
        apply structured_linear_continuation point pc f.locals
          (front ++ [Abs.integerVal op.output value.toNat]) after middle
        · simpa only [endpoint, pcEq] using continuation
        · rfl
        · simp only [middleEq, List.map_append, List.map_cons, List.map_nil, integerValue_type, frontTypes]
        · have labels : LabelsMatch (front ++ op.operands a b) f.labels targets := by
            simpa only [← split] using point.labels
          exact labels.replace_suffix heights
      refine .inl ⟨success, pc, { f with code := after, vals := front ++ [Abs.integerVal op.output value.toNat] },
        unchanged, ?_, nextPoint, nextTyped, ⟨rfl,rfl,rfl,rfl⟩,
        .tail _ _ _ _ _ (frame_references_numeric f front _ _ _ split), ?_⟩
      · simpa only [FrameSlots, List.append_assoc] using represented
      · apply ConcreteSim.of_source
        exact astep_simulation s ambient f rest after op _ typed sourceStep
end Exec.Interp
