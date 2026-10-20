import Exec.Interp.StructuredMachine.FloatChosenStructured
import Exec.Abs.Float.ChosenErasure
import Exec.Interp.Numeric.Float.FloatOwnership
namespace Exec.Interp.StructuredMachine
open Aeneas Aeneas.Std Abs.Float
variable {emission : FunctionEmission} [∀ compiled, FloatHeads (emission compiled)]

theorem step_float_chosen_structured_owned {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (numericChoice : choices.numeric=Spec.firstNumericChoice) (occurrence : Nat) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
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
        ChosenConcreteSim choices occurrence compiled.code.length raw.pc.val pc.val false false
          ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩ ⟨s, ambient, g :: rest, []⟩ ∧
        SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ∧
        FrameOwnershipClosure {f with code := op.source :: after} g ∧
        (g = {f with code := op.source :: after} ∨
        ChosenTransition choices occurrence ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩
          { f with code := op.source :: after } rest after op (.next ⟨s,ambient,g::rest,[]⟩))) ∨
      (∃ trap, out.1 = .Err (.Trap trap) ∧
        (trap = .IntegerOverflow ∨ trap = .InvalidConversionToInteger) ∧
        ∃ count, 0 < count ∧ Spec.ChosenStepsN choices occurrence count
          (Abs.decode ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩) []
          ⟨⟨s, ambient⟩, [.TRAP]⟩)) ⦄ := by
  apply WP.spec_mono (step_float_chosen_structured admissible numericChoice occurrence memory hooks floats allocator correct exec store platform index raw inst compiled
    C targets next output s ambient f rest op after last hf hi hc pcBound typed slots point)
  intro out effect
  obtain ⟨sameStore,samePlatform,effect⟩ := effect
  refine ⟨sameStore,samePlatform,?_⟩
  rcases effect with ⟨success,pc,g,unchanged,represented,nextPoint,nextTyped,metadata,simulation,prefixEffect,sourceStep⟩ | trap
  · have owned : FrameOwnershipClosure {f with code := op.source :: after} g := by
      rcases sourceStep with same | transition
      · rw [same]
        exact FrameOwnershipClosure.refl _
      · exact float_transition_frame_ownership s ambient f g rest after op (transition.erases admissible)
    exact Or.inl ⟨success,pc,g,unchanged,represented,nextPoint,nextTyped,metadata,simulation,prefixEffect,owned,sourceStep⟩
  · exact Or.inr trap
end Exec.Interp.StructuredMachine
