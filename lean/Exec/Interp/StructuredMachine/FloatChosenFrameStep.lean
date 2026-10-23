import Exec.Interp.StructuredMachine.LinearContinuation
import Exec.Interp.StructuredMachine.FloatHeads
import Exec.Interp.Numeric.Float.FloatChosenFetch
import Exec.Abs.Float.ChosenTransition
import Exec.Interp.Relations.ControlPoint
namespace Exec.Interp.StructuredMachine
open Aeneas Aeneas.Std Abs.Float
variable {emission : FunctionEmission} [∀ compiled, FloatHeads (emission compiled)]

theorem step_float_chosen_frame {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (numericChoice : choices.numeric = Spec.firstNumericChoice) (occurrence : Nat)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (op : Instruction) (after : List instr) (front : List val) (a b : Nat) (left right : U32)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : FramePoint emission s raw { f with code := op.source :: after } compiled C targets next output)
    (split : f.vals = front ++ op.operands a b)
    (first : a < 2^sizenn op.input) (second : b < 2^sizenn op.input)
    (leftPos : left.val = Code.slots ((f.locals ++ front).map Code.valueType))
    (rightPos : right.val = left.val + (op.arity - 1))
    (fetched : compiled.code.val[raw.pc.val]? = some (Code.floatInstruction op left left right))
    (continuation : Code.StructuredCodeWithTables (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (front.map Code.valueType ++ [valtype_numtype op.output]) after
      (raw.pc.val + 1) next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ((out.1 = .Ok () ∧ ∃ (pc : U32) (g : Abs.AFrame),
        { out.2.1 with slots := exec.slots } =
          { exec with frames := exec.frames.set index { raw with pc := pc } } ∧
        FrameSlots out.2.1 { raw with pc := pc } g ∧
        FramePoint emission s { raw with pc := pc } g compiled C targets next output ∧
        Abs.ATyped ⟨s, ambient, g :: rest, []⟩ ∧ FrameMetadata f g ∧
        Spec.ChoiceStep choices occurrence
          (Abs.decode ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩) [] (Abs.decode ⟨s, ambient, g :: rest, []⟩) ∧
        SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ∧
        ChosenTransition choices occurrence ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩
          { f with code := op.source :: after } rest after op (.next ⟨s,ambient,g::rest,[]⟩)) ∨
      (∃ trap, out.1 = .Err (.Trap trap) ∧
        (trap = .IntegerOverflow ∨ trap = .InvalidConversionToInteger) ∧
        ∃ count, 0 < count ∧ Spec.ChosenStepsN choices occurrence count
          (Abs.decode ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩) []
          ⟨⟨s, ambient⟩, [.TRAP]⟩)) ⦄ := by
  have frameTyped : Abs.FrameTyped s { f with code := op.source :: after } [] := by
    cases typed.frames with | cons h _ => exact h
  obtain ⟨frontWf, heights⟩ := op.prefix_bounds frameTyped front a b split
  have represented : ValuesAt exec.slots.val raw.base.val ((f.locals ++ front) ++ op.operands a b) := by
    simpa only [FrameSlots, split, List.append_assoc] using slots
  apply WP.spec_mono (step_float_chosen_values memory hooks floats allocator correct admissible numericChoice occurrence exec store platform index raw inst compiled
    op left right (f.locals ++ front) a b first second last hf hi hc fetched pcBound represented leftPos rightPos)
  intro out effect
  obtain ⟨sameStore, samePlatform, pc, pcEq, effect, prefixEffect⟩ := effect
  refine ⟨sameStore, samePlatform, ?_⟩
  rcases effect with ⟨bits, semantic, success, represented, unchanged⟩ | ⟨semantic, trap, kind, exactEffect⟩
  · have sourceStep : ChosenTransition choices occurrence ⟨s,ambient,{f with code := op.source :: after}::rest,[]⟩
        {f with code := op.source :: after} rest after op
        (.next ⟨s,ambient,{f with code := after, vals := front ++ [.CONST op.output (numberOfBits op.output bits)]}::rest,[]⟩) :=
      .next front a b bits split first second semantic
    have nextTyped := chosen_transition_preservation s ambient f rest after op _ typed sourceStep
    have nextPoint : FramePoint emission s {raw with pc := pc}
        {f with code := after, vals := front ++ [.CONST op.output (numberOfBits op.output bits)]}
        compiled C targets next output := by
      apply linear_continuation point pc f.locals
        (front ++ [val.CONST op.output (numberOfBits op.output bits)]) after
        (front.map Code.valueType ++ [valtype_numtype op.output])
      · simpa only [pcEq] using continuation
      · rfl
      · simp only [List.map_append, List.map_cons, List.map_nil, Code.valueType]
      · have labels : LabelsMatch (front ++ op.operands a b) f.labels targets := by
          simpa only [← split] using point.labels
        exact labels.replace_suffix heights
    refine .inl ⟨success,pc,_,unchanged,?_,nextPoint,nextTyped,⟨rfl,rfl,rfl,rfl⟩,?_,prefixEffect,sourceStep⟩
    · simpa only [FrameSlots,List.append_assoc] using represented
    · exact chosen_transition_simulation admissible s ambient f rest after op _ typed sourceStep
  · refine .inr ⟨trap,congrArg Prod.fst exactEffect,kind,?_⟩
    exact chosen_transition_trap_simulation admissible s ambient f rest after op typed (.trap front a b split first second semantic)
end Exec.Interp.StructuredMachine
