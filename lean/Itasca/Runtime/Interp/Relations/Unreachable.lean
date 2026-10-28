import Itasca.Runtime.Interp.Relations.Fetch
import Itasca.Runtime.Abs.Sim.Trap
import Itasca.Runtime.Abs.Sim.Typing

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem dispatch_unreachable_eq {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index inst function base : Usize) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index inst function base .Unreachable =
      .ok (.Err (.Trap .Unreachable), exec, store, platform) := by
  simp [runtime.interp.dispatch, runtime.interp.execute_unreachable, core.convert.IntoFrom.into,
    runtime.ExecError.Insts.CoreConvertFromTrap.from]

/-- The actual explicit trap has a positive counted SpecTec derivation through
all active labels and suspended frames, preserving the concrete store. -/
theorem step_unreachable_refines {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (fetched : compiled.code.val[raw.pc.val]? = some .Unreachable)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := .UNREACHABLE :: after } :: rest, []⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Err (.Trap .Unreachable) ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      (∃ pc : U32, pc.val = raw.pc.val + 1 ∧
        out.2.1 = { exec with frames := exec.frames.set index { raw with pc := pc } }) ∧
      ∃ n, 0 < n ∧ Spec.StepsHN n
        (Abs.decode ⟨s, ambient, { f with code := .UNREACHABLE :: after } :: rest, []⟩) []
        ⟨⟨s, ambient⟩, [.TRAP]⟩ ⦄ := by
  have frameTyped : Abs.FrameTyped s { f with code := .UNREACHABLE :: after } [] := by
    cases typed.frames with | cons h _ => exact h
  obtain ⟨wf, labels, values, code⟩ := Abs.frameTyped_wf frameTyped
  have remaining : Forall Abs.FrameWf rest := by
    cases typed.frames with | cons _ h => exact Abs.framesTyped_wf h
  have simulation := Abs.unreachable_simulation s ambient f rest after typed.store typed.ambient wf labels values
    (fun i hi => code i (by simp [hi])) remaining
  apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
    .Unreachable last hf hi hc fetched pcBound
  intro pc hpc
  rw [dispatch_unreachable_eq]
  exact ⟨rfl, rfl, rfl, ⟨pc, hpc, rfl⟩, simulation⟩

end Itasca.Runtime.Interp
