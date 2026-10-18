import Exec.Abs.Numeric.Decode
import Exec.Interp.Relations.Unreachable
import Exec.Interp.Relations.ControlPoint

namespace Exec.Interp
open Aeneas Aeneas.Std

theorem linearEmission_not_unreachable {locals before after emitted}
    (h : Code.LinearEmission locals before .UNREACHABLE emitted after) : False := by
  generalize equality : instr.UNREACHABLE = instruction at h
  cases h with
  | binary stack ity op left right hl hr => cases op <;> simp_all [Code.IntegerBinary.source]
  | numeric stack op a b ha hb =>
    have decoded := congrArg Abs.Numeric.decodeInstruction equality
    rw [Abs.Numeric.decodeInstruction_source] at decoded
    simp [Abs.Numeric.decodeInstruction_source, Abs.Numeric.decodeInstruction] at decoded
  | _ => simp_all

theorem codeRel_unreachable_inv {types functions returns locals code labels stack pc next output after}
    (relation : Code.CodeRel types functions returns locals code labels stack (.UNREACHABLE :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.CodeRel types functions returns locals code labels stack (.UNREACHABLE :: after) target.val next output) ∨
    code[pc]? = some .Unreachable := by
  cases relation with
  | linear head fragment rest => exact False.elim (linearEmission_not_unreachable head)
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | unreachable instruction remaining scope => exact Or.inr instruction

theorem step_unreachable_structured {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (functions : List functype) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := .UNREACHABLE :: after } :: rest, []⟩)
    (point : StructuredFramePoint raw { f with code := .UNREACHABLE :: after } compiled functions targets next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ pc : U32, out.2.1 = { exec with frames := exec.frames.set index { raw with pc := pc } } ∧
        ((out.1 = .Ok () ∧
          StructuredFramePoint { raw with pc := pc } { f with code := .UNREACHABLE :: after }
            compiled functions targets next output ∧
          ConcreteSim compiled.code.length raw.pc.val pc.val false false
            ⟨s, ambient, { f with code := .UNREACHABLE :: after } :: rest, []⟩
            ⟨s, ambient, { f with code := .UNREACHABLE :: after } :: rest, []⟩) ∨
         (out.1 = .Err (.Trap .Unreachable) ∧ ∃ n, 0 < n ∧ Spec.StepsHN n
           (Abs.decode ⟨s, ambient, { f with code := .UNREACHABLE :: after } :: rest, []⟩) []
           ⟨⟨s, ambient⟩, [.TRAP]⟩)) ⦄ := by
  rcases codeRel_unreachable_inv point.code.current with skip | fetched
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
      index raw inst compiled target last hf hi hc pcBound fetched)
    intro out effect
    obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
    exact ⟨sameStore, samePlatform, target, exactState, Or.inl ⟨success,
      ⟨point.labels, continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩,
      Or.inl ⟨rfl, dispatchMeasure_forward _ _ _ _ forward continuation.entry_bound⟩⟩⟩
  · apply WP.spec_mono (step_unreachable_refines memory hooks floats allocator exec store platform
      index raw inst compiled s ambient f rest after last hf hi hc pcBound fetched typed)
    intro out effect
    obtain ⟨trapped, sameStore, samePlatform, ⟨pc, _, exactState⟩, simulation⟩ := effect
    exact ⟨sameStore, samePlatform, pc, exactState, Or.inr ⟨trapped, simulation⟩⟩

end Exec.Interp
