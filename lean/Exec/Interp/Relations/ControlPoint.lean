import Exec.Interp.Control.StructuredPoint
import Exec.Interp.Control.PendingJump
import Exec.Abs.Sim.Typed

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Concrete control is either at the source instruction or at the retained
second half of a branch whose source operand transfer already occurred. -/
inductive ControlPoint (raw : runtime.interp.Frame) (source : Abs.AFrame)
    (compiled : runtime.bytecode.CompiledFunction) (functions : List functype)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype) : Bool → Prop where
  | ready (point : StructuredFramePoint raw source compiled functions targets next output) :
      ControlPoint raw source compiled functions targets next output false
  | jump (target : U32)
      (fetched : compiled.code.val[raw.pc.val]? = some (.Jump target))
      (continuation : StructuredFramePoint { raw with pc := target } source compiled functions targets next output) :
      ControlPoint raw source compiled functions targets next output true

/-- Simulation counts positive SpecTec reductions and explicitly measures all
concrete administrative dispatches. -/
def ConcreteSim (codeLength : Nat) (beforePC afterPC : Nat) (beforePending afterPending : Bool)
    (before after : Abs.AState) : Prop :=
  (Abs.decode before = Abs.decode after ∧
    dispatchMeasure afterPending codeLength afterPC after < dispatchMeasure beforePending codeLength beforePC before) ∨
  ∃ n, 0 < n ∧ Spec.StepsHN n (Abs.decode before) [] (Abs.decode after)

theorem dispatchMeasure_source_any {before after : Abs.AState}
    (beforePending afterPending : Bool) (codeLength pc target : Nat)
    (decrease : Abs.administrativeMeasure after < Abs.administrativeMeasure before) :
    dispatchMeasure afterPending codeLength target after < dispatchMeasure beforePending codeLength pc before := by
  have adjacent : Abs.administrativeMeasure after + 1 ≤ Abs.administrativeMeasure before := decrease
  have multiplied := Nat.mul_le_mul_right (2 * (codeLength + 1)) adjacent
  simp only [Nat.add_mul, Nat.one_mul] at multiplied
  cases beforePending <;> cases afterPending <;>
    simp only [dispatchMeasure, Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem ConcreteSim.of_source {before after : Abs.AState}
    (codeLength beforePC afterPC : Nat) (beforePending afterPending : Bool)
    (simulation : Abs.NextSim before after) :
    ConcreteSim codeLength beforePC afterPC beforePending afterPending before after := by
  rcases simulation with ⟨same, decrease⟩ | ⟨n, positive, steps⟩
  · exact Or.inl ⟨same, dispatchMeasure_source_any beforePending afterPending codeLength beforePC afterPC decrease⟩
  · exact Or.inr ⟨n, positive, steps⟩

theorem step_pendingStructuredJump {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (functions : List functype) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (source : Abs.AFrame) (rest : List Abs.AFrame)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (slots : FrameSlots exec raw source)
    (pending : ControlPoint raw source compiled functions targets next output true) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ target : U32,
        out.2.1 = { exec with frames := exec.frames.set index { raw with pc := target } } ∧
        FrameSlots out.2.1 { raw with pc := target } source ∧
        ControlPoint { raw with pc := target } source compiled functions targets next output false ∧
        ConcreteSim compiled.code.length raw.pc.val target.val true false
          ⟨s, ambient, source :: rest, []⟩ ⟨s, ambient, source :: rest, []⟩ ⦄ := by
  cases pending with
  | jump target fetched continuation =>
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
      index raw inst compiled target last hf hi hc pcBound fetched)
    intro out effect
    obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
    refine ⟨success, sameStore, samePlatform, target, exactState, ?_, .ready continuation, ?_⟩
    · rw [exactState]
      exact slots
    · exact Or.inl ⟨rfl, dispatchMeasure_jump _ _ _ _⟩

end Exec.Interp
