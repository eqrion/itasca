import Itasca.Runtime.Interp.Machine.Normalization.LinearContinuation
import Itasca.Runtime.Interp.Machine.Coverage.OrdinaryHeads
import Itasca.Runtime.Interp.Numeric.Float.FloatFetch
import Itasca.Runtime.SourceMachine.Float.Transition
import Itasca.Runtime.Interp.Relations.ControlPoint
import Itasca.Runtime.Interp.Machine.Normalization.IndexedLinear
import Itasca.Runtime.Interp.Machine.Emission.Integer
import Itasca.Runtime.Compiler.Local.Lowering.Float.FloatEmissionInversion
import Itasca.Runtime.Interp.Numeric.Float.FloatOwnership

/-!
Floating-point structured execution and ownership. A frame step lifts through the structured machine to preserve the execution relation and owned source values.
-/

/-! ## Float Frame Step -/

section

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std SourceMachine.Float
theorem step_float_frame {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (op : Instruction) (after : List instr) (front : List val) (a b : Nat) (left right : U32)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : FramePoint s raw { f with code := op.source :: after } compiled C targets next output)
    (split : f.vals = front ++ op.operands a b)
    (first : a < 2^sizenn op.input) (second : b < 2^sizenn op.input)
    (leftPos : left.val = Compiler.slots ((f.locals ++ front).map Compiler.valueType))
    (rightPos : right.val = left.val + (op.arity - 1))
    (fetched : compiled.code.val[raw.pc.val]? = some (Compiler.floatInstruction op left left right))
    (continuation : Compiler.StructuredCode (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (front.map Compiler.valueType ++ [valtype_numtype op.output]) after
      (raw.pc.val + 1) next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ((out.1 = .Ok () ∧ ∃ (pc : U32) (g : SourceMachine.AFrame),
        { out.2.1 with slots := exec.slots } =
          { exec with frames := exec.frames.set index { raw with pc := pc } } ∧
        FrameSlots out.2.1 { raw with pc := pc } g ∧
        FramePoint s { raw with pc := pc } g compiled C targets next output ∧
        SourceMachine.ATyped ⟨s, ambient, g :: rest, []⟩ ∧ FrameMetadata f g ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false
          ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩ ⟨s, ambient, g :: rest, []⟩ ∧
        SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ∧
        Transition ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩
          { f with code := op.source :: after } rest after op (.next ⟨s,ambient,g::rest,[]⟩)) ∨
      (∃ trap, out.1 = .Err (.Trap trap) ∧
        (trap = .IntegerOverflow ∨ trap = .InvalidConversionToInteger) ∧
        ∃ count, 0 < count ∧ Spec.StepsHN count
          (SourceMachine.decode ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩) []
          ⟨⟨s, ambient⟩, [.TRAP]⟩)) ⦄ := by
  have frameTyped : SourceMachine.FrameTyped s { f with code := op.source :: after } [] := by
    cases typed.frames with | cons h _ => exact h
  obtain ⟨frontWf, heights⟩ := op.prefix_bounds frameTyped front a b split
  have represented : ValuesAt exec.slots.val raw.base.val ((f.locals ++ front) ++ op.operands a b) := by
    simpa only [FrameSlots, split, List.append_assoc] using slots
  apply WP.spec_mono (step_float_values memory hooks floats allocator correct exec store platform index raw inst compiled
    op left right (f.locals ++ front) a b first second last hf hi hc fetched pcBound represented leftPos rightPos)
  intro out effect
  obtain ⟨sameStore, samePlatform, pc, pcEq, effect, prefixEffect⟩ := effect
  refine ⟨sameStore, samePlatform, ?_⟩
  rcases effect with ⟨bits, semantic, success, represented, unchanged⟩ | ⟨semantic, trap, kind, exactEffect⟩
  · have sourceStep : Transition ⟨s,ambient,{f with code := op.source :: after}::rest,[]⟩
        {f with code := op.source :: after} rest after op
        (.next ⟨s,ambient,{f with code := after, vals := front ++ [.CONST op.output (numberOfBits op.output bits)]}::rest,[]⟩) :=
      .next front a b bits split first second semantic
    have nextTyped := transition_preservation s ambient f rest after op _ typed sourceStep
    have nextPoint : FramePoint s {raw with pc := pc}
        {f with code := after, vals := front ++ [.CONST op.output (numberOfBits op.output bits)]}
        compiled C targets next output := by
      apply linear_continuation point pc f.locals
        (front ++ [val.CONST op.output (numberOfBits op.output bits)]) after
        (front.map Compiler.valueType ++ [valtype_numtype op.output])
      · simpa only [pcEq] using continuation
      · rfl
      · simp only [List.map_append, List.map_cons, List.map_nil, Compiler.valueType]
      · have labels : LabelsMatch (front ++ op.operands a b) f.labels targets := by
          simpa only [← split] using point.labels
        exact labels.replace_suffix heights
    refine .inl ⟨success,pc,_,unchanged,?_,nextPoint,nextTyped,⟨rfl,rfl,rfl,rfl⟩,?_,prefixEffect,sourceStep⟩
    · simpa only [FrameSlots,List.append_assoc] using represented
    · apply ConcreteSim.of_source
      exact transition_simulation s ambient f rest after op _ typed sourceStep
  · refine .inr ⟨trap,congrArg Prod.fst exactEffect,kind,?_⟩
    exact transition_trap_simulation s ambient f rest after op typed (.trap front a b split first second semantic)
end Itasca.Runtime.Interp.Machine

end

/-! ## Float Structured -/

section

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std SourceMachine.Float
theorem step_float_structured {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (op : Instruction) (after : List instr)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : FramePoint s raw { f with code := op.source :: after } compiled C targets next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ((out.1 = .Ok () ∧ ∃ (pc : U32) (g : SourceMachine.AFrame),
        { out.2.1 with slots := exec.slots } =
          { exec with frames := exec.frames.set index { raw with pc := pc } } ∧
        FrameSlots out.2.1 { raw with pc := pc } g ∧
        FramePoint s { raw with pc := pc } g compiled C targets next output ∧
        SourceMachine.ATyped ⟨s, ambient, g :: rest, []⟩ ∧ FrameMetadata f g ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false
          ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩ ⟨s, ambient, g :: rest, []⟩ ∧
        SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ∧
        (g = {f with code := op.source :: after} ∨
        Transition ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩
          { f with code := op.source :: after } rest after op (.next ⟨s,ambient,g::rest,[]⟩))) ∨
      (∃ trap, out.1 = .Err (.Trap trap) ∧
        (trap = .IntegerOverflow ∨ trap = .InvalidConversionToInteger) ∧
        ∃ count, 0 < count ∧ Spec.StepsHN count
          (SourceMachine.decode ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩) []
          ⟨⟨s, ambient⟩, [.TRAP]⟩)) ⦄ := by
  have linear : linearSource op.source = true := by
    cases op <;> rfl
  rcases structured_code_linear_inv linear point.code.current with skip | branch
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    have targetPoint : FramePoint s {raw with pc := target}
        {f with code := op.source :: after} compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels,⟨continuation,point.code.targets,point.code.normal,point.code.exit,point.code.root⟩⟩
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
      index raw inst compiled target last hf hi hc pcBound fetched)
    intro out effect
    obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
    refine ⟨sameStore,samePlatform,.inl ⟨success,target,{f with code := op.source :: after},
      ?_,?_,targetPoint,typed,⟨rfl,rfl,rfl,rfl⟩,?_,?_,Or.inl rfl⟩⟩
    · rw [exactState]
    · rw [exactState]
      exact slots
    · exact Or.inl ⟨rfl,dispatch_measure_forward _ _ _ _ forward continuation.entry_bound⟩
    · rw [exactState]
      exact SlotPrefix.refl _ _
  · obtain ⟨middle,emitted,tail,head,fragment,continuation⟩ := branch
    obtain ⟨stack,left,right,shape,middleEq,emittedEq,leftPos,rightPos⟩ := (FloatHeads.project (.float op) head).float_inv op
    have frameTyped : SourceMachine.FrameTyped s {f with code := op.source :: after} [] := by
      cases typed.frames with | cons h _ => exact h
    obtain ⟨front,a,b,split,first,second,frontWf,heights⟩ := op.typed_operands frameTyped
    have frontTypes : front.map Compiler.valueType = stack := by
      have types : (op.operands a b).map Compiler.valueType = List.replicate op.arity (valtype_numtype op.input) := by
        simpa only [show Compiler.valueType = SourceMachine.valueType from funext value_type_eq_abs] using op.operands_types a b
      rw [split,List.map_append,types] at shape
      exact List.append_cancel_right shape
    have leftPosition : left.val = Compiler.slots ((f.locals ++ front).map Compiler.valueType) := by
      simpa only [point.locals,List.map_append,Compiler.slots_append,frontTypes] using leftPos
    have fetched : compiled.code.val[raw.pc.val]? = some (Compiler.floatInstruction op left left right) := by
      simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [emittedEq,List.getElem?_cons_zero])
    have endpoint : tail = raw.pc.val + 1 := by
      obtain ⟨_,_,_,_,h⟩ := fragment
      simpa only [emittedEq,List.length_singleton] using h
    have remaining : Compiler.StructuredCode (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
        compiled.code.val compiled.jump_tables.val targets (front.map Compiler.valueType ++ [valtype_numtype op.output]) after
        (raw.pc.val+1) next output := by
      simpa only [endpoint,middleEq,frontTypes] using continuation
    apply WP.spec_mono (step_float_frame memory hooks floats allocator correct exec store platform index raw inst compiled
      C targets next output s ambient f rest op after front a b left right last hf hi hc pcBound typed slots point
      split first second leftPosition rightPos fetched remaining)
    intro out effect
    obtain ⟨sameStore,samePlatform,effect⟩ := effect
    refine ⟨sameStore,samePlatform,?_⟩
    rcases effect with ⟨success,pc,g,unchanged,represented,nextPoint,nextTyped,metadata,simulation,prefixEffect,transition⟩ | trap
    · exact Or.inl ⟨success,pc,g,unchanged,represented,nextPoint,nextTyped,metadata,simulation,prefixEffect,Or.inr transition⟩
    · exact Or.inr trap
end Itasca.Runtime.Interp.Machine

end

/-! ## Float Structured Owned -/

section

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std SourceMachine.Float
theorem step_float_structured_owned {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (op : Instruction) (after : List instr)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : FramePoint s raw { f with code := op.source :: after } compiled C targets next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ((out.1 = .Ok () ∧ ∃ (pc : U32) (g : SourceMachine.AFrame),
        { out.2.1 with slots := exec.slots } =
          { exec with frames := exec.frames.set index { raw with pc := pc } } ∧
        FrameSlots out.2.1 { raw with pc := pc } g ∧
        FramePoint s { raw with pc := pc } g compiled C targets next output ∧
        SourceMachine.ATyped ⟨s, ambient, g :: rest, []⟩ ∧ FrameMetadata f g ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false
          ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩ ⟨s, ambient, g :: rest, []⟩ ∧
        SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ∧
        FrameOwnershipClosure {f with code := op.source :: after} g ∧
        (g = {f with code := op.source :: after} ∨
        Transition ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩
          { f with code := op.source :: after } rest after op (.next ⟨s,ambient,g::rest,[]⟩))) ∨
      (∃ trap, out.1 = .Err (.Trap trap) ∧
        (trap = .IntegerOverflow ∨ trap = .InvalidConversionToInteger) ∧
        ∃ count, 0 < count ∧ Spec.StepsHN count
          (SourceMachine.decode ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩) []
          ⟨⟨s, ambient⟩, [.TRAP]⟩)) ⦄ := by
  apply WP.spec_mono (step_float_structured memory hooks floats allocator correct exec store platform index raw inst compiled
    C targets next output s ambient f rest op after last hf hi hc pcBound typed slots point)
  intro out effect
  obtain ⟨sameStore,samePlatform,effect⟩ := effect
  refine ⟨sameStore,samePlatform,?_⟩
  rcases effect with ⟨success,pc,g,unchanged,represented,nextPoint,nextTyped,metadata,simulation,prefixEffect,sourceStep⟩ | trap
  · have owned : FrameOwnershipClosure {f with code := op.source :: after} g := by
      rcases sourceStep with same | transition
      · rw [same]
        exact FrameOwnershipClosure.refl _
      · exact float_transition_frame_ownership s ambient f g rest after op transition
    exact Or.inl ⟨success,pc,g,unchanged,represented,nextPoint,nextTyped,metadata,simulation,prefixEffect,owned,sourceStep⟩
  · exact Or.inr trap
end Itasca.Runtime.Interp.Machine

end
