import Exec.Interp.StructuredMachine.IndexedLinear
import Exec.Interp.StructuredMachine.FloatFrameStep
import Exec.Interp.Core.Linear
import Exec.Code.Local.Lowering.Float.FloatEmissionInversion
import Exec.Interp.StructuredMachine.LinearContinuation
import Exec.Interp.StructuredMachine.FloatHeads
import Exec.Interp.Numeric.Float.FloatFetch
import Exec.Abs.Float.Transition
import Exec.Interp.Relations.ControlPoint
namespace Exec.Interp.StructuredMachine
open Aeneas Aeneas.Std Abs.Float
variable {emission : FunctionEmission} [∀ compiled, FloatHeads (emission compiled)]

theorem step_float_structured {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
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
    (typed : Abs.ATyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : FramePoint emission s raw { f with code := op.source :: after } compiled C targets next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ((out.1 = .Ok () ∧ ∃ (pc : U32) (g : Abs.AFrame),
        { out.2.1 with slots := exec.slots } =
          { exec with frames := exec.frames.set index { raw with pc := pc } } ∧
        FrameSlots out.2.1 { raw with pc := pc } g ∧
        FramePoint emission s { raw with pc := pc } g compiled C targets next output ∧
        Abs.ATyped ⟨s, ambient, g :: rest, []⟩ ∧ FrameMetadata f g ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false
          ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩ ⟨s, ambient, g :: rest, []⟩ ∧
        SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ∧
        (g = {f with code := op.source :: after} ∨
        Transition ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩
          { f with code := op.source :: after } rest after op (.next ⟨s,ambient,g::rest,[]⟩))) ∨
      (∃ trap, out.1 = .Err (.Trap trap) ∧
        (trap = .IntegerOverflow ∨ trap = .InvalidConversionToInteger) ∧
        ∃ count, 0 < count ∧ Spec.StepsHN count
          (Abs.decode ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩) []
          ⟨⟨s, ambient⟩, [.TRAP]⟩)) ⦄ := by
  have linear : linearSource op.source = true := by
    cases op <;> rfl
  rcases structuredCodeWithTables_linear_inv linear point.code.current with skip | branch
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    have targetPoint : FramePoint emission s {raw with pc := target}
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
    · exact Or.inl ⟨rfl,dispatchMeasure_forward _ _ _ _ forward continuation.entry_bound⟩
    · rw [exactState]
      exact SlotPrefix.refl _ _
  · obtain ⟨middle,emitted,tail,head,fragment,continuation⟩ := branch
    obtain ⟨stack,left,right,shape,middleEq,emittedEq,leftPos,rightPos⟩ := (FloatHeads.project (.scalar op) head).float_inv op
    have frameTyped : Abs.FrameTyped s {f with code := op.source :: after} [] := by
      cases typed.frames with | cons h _ => exact h
    obtain ⟨front,a,b,split,first,second,frontWf,heights⟩ := op.typed_operands frameTyped
    have frontTypes : front.map Code.valueType = stack := by
      have types : (op.operands a b).map Code.valueType = List.replicate op.arity (valtype_numtype op.input) := by
        simpa only [show Code.valueType = Abs.valueType from funext valueType_eq_abs] using op.operands_types a b
      rw [split,List.map_append,types] at shape
      exact List.append_cancel_right shape
    have leftPosition : left.val = Code.slots ((f.locals ++ front).map Code.valueType) := by
      simpa only [point.locals,List.map_append,Code.slots_append,frontTypes] using leftPos
    have fetched : compiled.code.val[raw.pc.val]? = some (Code.floatInstruction op left left right) := by
      simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [emittedEq,List.getElem?_cons_zero])
    have endpoint : tail = raw.pc.val + 1 := by
      obtain ⟨_,_,_,_,h⟩ := fragment
      simpa only [emittedEq,List.length_singleton] using h
    have remaining : Code.StructuredCodeWithTables (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
        compiled.code.val compiled.jump_tables.val targets (front.map Code.valueType ++ [valtype_numtype op.output]) after
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
end Exec.Interp.StructuredMachine
