import Exec.Interp.StructuredMachine.IndexedLinear
import Exec.Interp.StructuredMachine.NumericInversion
import Exec.Interp.Relations.ReferenceTransfers
import Exec.Interp.Relations.SourceClosure
import Exec.Interp.StructuredMachine.LinearContinuation
import Exec.Interp.Relations.PrefixDispatch
import Exec.Abs.Core.Correct
import Exec.Interp.Relations.ControlPoint
import Exec.Interp.Numeric.Integer.NumericFetch
import Exec.Interp.Numeric.Integer.NumericCodePoint
import Exec.Abs.Numeric.TransitionSimulation

namespace Exec.Interp.StructuredMachine
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
end Exec.Interp.StructuredMachine
