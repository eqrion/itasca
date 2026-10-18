import Exec.Interp.Relations.ReferenceTransfers
import Exec.Interp.Relations.SourceClosure
import Exec.Interp.Core.Linear
import Exec.Interp.Relations.PrefixDispatch
import Exec.Abs.Core.Correct
import Exec.Interp.Relations.ControlPoint
import Exec.Interp.Numeric.Integer.NumericFetch
import Exec.Interp.Numeric.Integer.NumericCodePoint
import Exec.Abs.Numeric.TransitionSimulation

namespace Exec.Interp
open Aeneas Aeneas.Std Abs.Numeric

theorem step_numeric_core {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (op : Instruction) (after : List instr)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (typed : Abs.CoreTyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : CoreFramePoint s raw { f with code := op.source :: after }
      compiled C targets next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ((out.1 = .Ok () ∧
      ∃ (pc : U32) (g : Abs.AFrame),
        { out.2.1 with slots := exec.slots } =
          { exec with frames := exec.frames.set index { raw with pc := pc } } ∧
        FrameSlots out.2.1 { raw with pc := pc } g ∧
        CoreFramePoint s { raw with pc := pc } g compiled C targets next output ∧
        Abs.CoreTyped ⟨s, ambient, g :: rest, []⟩ ∧
        FrameMetadata f g ∧
        SourceClosure { f with code := op.source :: after } g ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false
          ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩
          ⟨s, ambient, g :: rest, []⟩ ∧
        SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ∧
        (g = {f with code := op.source :: after} ∨
          Abs.Core.step ⟨s,ambient,{f with code := op.source :: after} :: rest,[]⟩ = .next ⟨s,ambient,g::rest,[]⟩)) ∨
      (∃ trap, out.1 = .Err (.Trap trap) ∧
        (trap = .IntegerDivideByZero ∨ trap = .IntegerOverflow) ∧
        ∃ count, 0 < count ∧ Spec.StepsHN count
          (Abs.decode ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩) []
          ⟨⟨s, ambient⟩, [.TRAP]⟩)) ⦄ := by
  have linear : linearSource op.source = true := by
    cases op <;> (try casesm* Conversion) <;> rfl
  rcases structuredCode_linear_inv linear point.code.current with skip | branch
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    have targetPoint : CoreFramePoint s { raw with pc := target }
        { f with code := op.source :: after } compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels, ⟨continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩⟩
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
      index raw inst compiled target last hf hi hc pcBound fetched)
    intro out effect
    obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
    refine ⟨sameStore, samePlatform, .inl ⟨success, target, { f with code := op.source :: after },
      ?_, ?_, targetPoint, typed, ⟨rfl, rfl, rfl, rfl⟩, .refl _, ?_,?_,Or.inl rfl⟩⟩
    · rw [exactState]
    · rw [exactState]
      exact slots
    · exact Or.inl ⟨rfl, dispatchMeasure_forward _ _ _ _ forward continuation.entry_bound⟩
    · rw [exactState]
      exact SlotPrefix.refl _ _
  · obtain ⟨middle, emitted, tail, head, fragment, continuation⟩ := branch
    obtain ⟨stack, left, right, shape, emittedEq, middleEq, leftPos, rightPos⟩ := linearEmission_numeric_inv op (coreEmission_numeric_pure op head)
    have frameTyped : Abs.FrameTyped s { f with code := op.source :: after } [] := by
      cases typed.typed.frames with | cons h _ => exact h
    obtain ⟨front, a, b, split, wfFront, heights⟩ := op.typed_operands_bounds frameTyped
    have frontTypes : front.map Code.valueType = stack := by
      rw [split, List.map_append, numericOperand_types] at shape
      exact List.append_cancel_right shape
    have leftPosition : left.val = Code.slots ((f.locals ++ front).map Code.valueType) := by
      simpa only [point.locals,List.map_append, Code.slots_append, frontTypes] using leftPos
    have fetched : compiled.code.val[raw.pc.val]? = some (Code.integerInstruction op left left right) := by
      simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [emittedEq, List.getElem?_cons_zero])
    have endpoint : tail = raw.pc.val + 1 := by
      obtain ⟨_, _, _, _, h⟩ := fragment
      simpa only [emittedEq, List.length_singleton] using h
    have represented : ValuesAt exec.slots.val raw.base.val ((f.locals ++ front) ++ op.operands a b) := by
      simpa only [FrameSlots, split, List.append_assoc] using slots
    obtain ⟨out,returned,effect⟩ := WP.spec_imp_exists (step_integer_values memory hooks floats allocator exec store platform index raw inst compiled
      op left right (f.locals ++ front) a b last hf hi hc fetched pcBound represented leftPosition rightPos)
    rw [returned]
    simp only [WP.spec_ok]
    have prefixEffect := step_prefix memory hooks floats allocator exec store platform index raw inst compiled
      (Code.integerInstruction op left left right) last hf hi hc fetched (.numeric op left left right) out returned
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
      exact astep_trap_simulation s ambient f rest after op typed.typed sourceTrap
    | some value =>
      simp only [NumericValuesEffect, operation] at effect
      obtain ⟨success, represented, unchanged⟩ := effect
      have sourceStep : Abs.astep ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩ = .next
          ⟨s, ambient, { f with code := after, vals := front ++ [Abs.integerVal op.output value.toNat] } :: rest, []⟩ := by
        have h := astep_operands ⟨s, ambient, [], []⟩ f rest after front op a b
        simp only [finish, operation, Abs.advance] at h
        simpa only [← split] using h
      have nextTyped := Abs.instruction_preservation s ambient f rest _ after _ (.numeric op) typed.typed sourceStep
      have nextPoint : CoreFramePoint s { raw with pc := pc }
          { f with code := after, vals := front ++ [Abs.integerVal op.output value.toNat] }
          compiled C targets next output := by
        apply core_structured_linear_continuation point pc f.locals
          (front ++ [Abs.integerVal op.output value.toNat]) after middle
        · simpa only [endpoint, pcEq] using continuation
        · rfl
        · simp only [middleEq, List.map_append, List.map_cons, List.map_nil, integerValue_type, frontTypes]
        · have labels : LabelsMatch (front ++ op.operands a b) f.labels targets := by
            simpa only [← split] using point.labels
          exact labels.replace_suffix heights
      refine .inl ⟨success, pc, { f with code := after, vals := front ++ [Abs.integerVal op.output value.toNat] },
        unchanged, ?_, nextPoint, ⟨nextTyped,typed.contents⟩, ⟨rfl,rfl,rfl,rfl⟩,
        .tail _ _ _ _ _ (frame_references_numeric f front _ _ _ split), ?_,prefixEffect,Or.inr ?_⟩
      · simpa only [FrameSlots, List.append_assoc] using represented
      · apply ConcreteSim.of_source
        exact astep_simulation s ambient f rest after op _ typed.typed sourceStep
      · change Abs.Core.instruction s ambient {f with code := op.source :: after} rest op.source after = _
        rw [Abs.Core.instruction_slice s ambient {f with code := op.source :: after} rest op.source after (.numeric op) frameTyped]
        exact sourceStep

end Exec.Interp
