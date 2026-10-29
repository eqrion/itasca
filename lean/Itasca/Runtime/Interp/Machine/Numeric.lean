import Itasca.Runtime.Interp.Machine.Coverage.OrdinaryHeads
import Itasca.Runtime.Interp.Machine.Emission.Integer
import Itasca.Runtime.Interp.Machine.Normalization.IndexedLinear
import Itasca.Runtime.Interp.Relations.ReferenceTransfers
import Itasca.Runtime.Interp.Relations.SourceClosure
import Itasca.Runtime.Interp.Machine.Normalization.LinearContinuation
import Itasca.Runtime.Interp.Relations.PrefixDispatch
import Itasca.Runtime.SourceMachine.Core.Correct
import Itasca.Runtime.Interp.Relations.ControlPoint
import Itasca.Runtime.Interp.Numeric.Integer.NumericFetch
import Itasca.Runtime.Interp.Numeric.Integer.NumericCodePoint
import Itasca.Runtime.SourceMachine.Numeric.TransitionSimulation
import Itasca.Runtime.Interp.Machine.Progress.OrdinaryExecution
import Itasca.Runtime.Spec.Extend
import Itasca.Runtime.SourceMachine.Numeric.Positive
import Itasca.Runtime.Interp.Machine.Control.UniformSource
import Itasca.Runtime.Interp.Machine.Coverage.SupportedControlSemantics
import Itasca.Runtime.SourceMachine.Core.Bound
import Itasca.Runtime.SourceMachine.Ownership.Core

/-!
Integer numeric machine fetch, execution and trap classification. The resulting argument is consumed by complete machine advance while preserving its source grammar and store premises.
-/

/-! ## Numeric Inversion -/

section

namespace Itasca.Runtime.Interp.StructuredMachine
open Aeneas Aeneas.Std
theorem emission_numeric_pure {compiled C before after emitted} (op : Abs.Numeric.Instruction)
    (head : Interp.emission compiled C before op.source emitted after) :
    Code.LinearEmission C.LOCALS before op.source emitted after :=
  scalarEmission_numeric_pure op (FloatHeads.project (.core (.pure (.numeric op))) head)
end Itasca.Runtime.Interp.StructuredMachine

end

/-! ## Numeric -/

section

namespace Itasca.Runtime.Interp.StructuredMachine
open Aeneas Aeneas.Std Abs.Numeric
theorem step_numeric {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
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
    (point : FramePoint s raw { f with code := op.source :: after }
      compiled C targets next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ((out.1 = .Ok () ∧
      ∃ (pc : U32) (g : Abs.AFrame),
        { out.2.1 with slots := exec.slots } =
          { exec with frames := exec.frames.set index { raw with pc := pc } } ∧
        FrameSlots out.2.1 { raw with pc := pc } g ∧
        FramePoint s { raw with pc := pc } g compiled C targets next output ∧
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
    have targetPoint : FramePoint s { raw with pc := target }
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
    obtain ⟨stack, left, right, shape, emittedEq, middleEq, leftPos, rightPos⟩ := linearEmission_numeric_inv op (emission_numeric_pure op head)
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
      have nextPoint : FramePoint s { raw with pc := pc }
          { f with code := after, vals := front ++ [Abs.integerVal op.output value.toNat] }
          compiled C targets next output := by
        apply linear_continuation point pc f.locals
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

end Itasca.Runtime.Interp.StructuredMachine

end

/-! ## Numeric Fetch -/

section

namespace Itasca.Runtime.Interp.StructuredMachine
open Aeneas Aeneas.Std Abs.Numeric
theorem numeric_fetched {raw compiled C targets next output s} {f : Abs.AFrame}
    (op : Instruction) (after : List instr)
    (point : FramePoint s raw {f with code := op.source :: after} compiled C targets next output) :
    ∃ instruction, compiled.code.val[raw.pc.val]? = some instruction := by
  have linear : linearSource op.source = true := by cases op <;> (try casesm* Conversion) <;> rfl
  rcases structuredCode_linear_inv linear point.code.current with ⟨target,forward,fetch,tail⟩ | ⟨middle,emitted,tail,head,fragment,rest⟩
  · exact ⟨_,fetch⟩
  · obtain ⟨stack,left,right,shape,emittedEq,middleEq,leftPos,rightPos⟩ := linearEmission_numeric_inv op (emission_numeric_pure op head)
    refine ⟨Code.integerInstruction op left left right,?_⟩
    simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [emittedEq,List.getElem?_cons_zero])

end Itasca.Runtime.Interp.StructuredMachine

end

/-! ## Numeric Execution Owned -/

section

namespace Itasca.Runtime.Interp.StructuredMachine
open Aeneas Aeneas.Std Abs.Numeric

theorem step_numeric_execution_owned_uniform {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (op : Instruction) (after : List instr)
    (last : index.val+1 = exec.frames.length) (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := op.source :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := op.source :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ((out.1 = .Ok () ∧ ∃ pc : U32, ∃ g : Abs.AFrame,
        Execution view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        UniformConcreteSim raw.pc.val pc.val false false initial ⟨initial.store,ambient,g::rest,[]⟩ [] ∧
        (∀ bounds, Abs.Ownership.StatefulOwned bounds initial → Abs.Ownership.StatefulOwned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩)) ∨
      (∃ trap, out.1 = .Err (.Trap trap) ∧ (trap = .IntegerDivideByZero ∨ trap = .IntegerOverflow) ∧
        ∃ count, 0 < count ∧ Spec.StepsHN count (Abs.decode initial) [] ⟨⟨initial.store,ambient⟩,[.TRAP]⟩)) ⦄ := by
  dsimp only
  obtain ⟨instruction,fetched⟩ := numeric_fetched op after point
  have pcBound := program.fetched_bound instruction fetched
  apply WP.spec_mono (step_numeric memory hooks floats allocator exec store platform index raw inst compiled C targets
    next output (Store.decodeStore view code store) ambient f rest op after last hf hi hc pcBound machine.typed slots point)
  intro out effect
  refine ⟨effect.1,effect.2.1,?_⟩
  rcases effect.2.2 with success | trapped
  · obtain ⟨status,pc,g,unchanged,represented,continuation,fresh,metadata,closure,simulation,prefixEffect,sourceStep⟩ := success
    have uniform : UniformConcreteSim raw.pc.val pc.val false false
        ⟨Store.decodeStore view code store,ambient,{f with code := op.source::after}::rest,[]⟩
        ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ [] := by
      rcases sourceStep with same | step
      · subst g
        exact simulation.uniform_same (by scalar_tac)
      · exact UniformConcreteSim.single (Abs.Numeric.core_step_positive _ _ _ _ _ _ _ machine.typed.typed step)
    have covered : Abs.SupportedState ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
      rcases sourceStep with same | step
      · simpa only [same] using machine.core
      · exact StructuredMachine.core_step_supported machine.typed machine.core step
    have ownership : ∀ bounds, Abs.Ownership.StatefulOwned bounds ⟨Store.decodeStore view code store,ambient,{f with code := op.source :: after}::rest,[]⟩ →
        Abs.Ownership.StatefulOwned bounds ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
      intro bounds bounded
      rcases sourceStep with same | step
      · simpa only [same] using bounded
      · exact StructuredMachine.core_step_owned machine.typed machine.core step bounds bounded
    refine Or.inl ⟨status,pc,g,?_,simulation,uniform,ownership,StructuredMachine.bound_transition machine.typed machine.core (sourceStep.imp_left (fun same => by rw [same]))⟩
    exact machine.ordinary view code ambient {f with code := op.source :: after} g rest expected raw.pc.val false
      (.refl store) (Spec.extend_store_refl _ machine.typed.typed.store) raw index pc last hf program (.ready continuation)
      represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ unchanged prefixEffect fresh covered
  · exact Or.inr trapped
theorem step_numeric_execution_owned {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (op : Instruction) (after : List instr)
    (last : index.val+1 = exec.frames.length) (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := op.source :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := op.source :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ((out.1 = .Ok () ∧ ∃ pc : U32, ∃ g : Abs.AFrame,
        Execution view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        (∀ bounds, Abs.Ownership.StatefulOwned bounds initial → Abs.Ownership.StatefulOwned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩)) ∨
      (∃ trap, out.1 = .Err (.Trap trap) ∧ (trap = .IntegerDivideByZero ∨ trap = .IntegerOverflow) ∧
        ∃ count, 0 < count ∧ Spec.StepsHN count (Abs.decode initial) [] ⟨⟨initial.store,ambient⟩,[.TRAP]⟩)) ⦄ := by
  apply WP.spec_mono (step_numeric_execution_owned_uniform memory hooks floats allocator view code exec store platform index raw inst compiled C targets next output ambient f rest op after last hf hi hc program slots point expected machine)
  rintro out ⟨same,platform,success | trapped⟩
  · rcases success with ⟨success,pc,g,machine,simulation,uniform,ownership,bounded⟩
    exact ⟨same,platform,Or.inl ⟨success,pc,g,machine,simulation,ownership,bounded⟩⟩
  · exact ⟨same,platform,Or.inr trapped⟩

end Itasca.Runtime.Interp.StructuredMachine

end

/-! ## Numeric No Trap -/

section

namespace Itasca.Runtime.Interp.StructuredMachine
open Aeneas Aeneas.Std Abs.Numeric

theorem step_numeric_no_trap {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (op : Instruction) (after : List instr)
    (total : ∀ a b, op.apply a b ≠ none)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (typed : Abs.CoreTyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : FramePoint s raw { f with code := op.source :: after }
      compiled C targets next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out => out.1 = .Ok () ⦄ := by
  have linear : linearSource op.source = true := by
    cases op <;> (try casesm* Conversion) <;> rfl
  rcases structuredCode_linear_inv linear point.code.current with skip | branch
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
      index raw inst compiled target last hf hi hc pcBound fetched)
    intro out effect
    obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
    exact success
  · obtain ⟨middle, emitted, tail, head, fragment, continuation⟩ := branch
    obtain ⟨stack, left, right, shape, emittedEq, middleEq, leftPos, rightPos⟩ := linearEmission_numeric_inv op (emission_numeric_pure op head)
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
    obtain ⟨sameStore,samePlatform,pc,pcEq,effect⟩ := effect
    cases operation : op.apply a b with
    | none => exact False.elim (total a b operation)
    | some value =>
      simp only [NumericValuesEffect,operation] at effect
      exact effect.1
end Itasca.Runtime.Interp.StructuredMachine

end
