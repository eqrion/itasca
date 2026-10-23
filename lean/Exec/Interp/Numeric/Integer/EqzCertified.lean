import Exec.Interp.Numeric.Integer.EqzDispatch
import Exec.Interp.Numeric.Integer.EqzCodePoint

/-! A complete concrete iteration whose fetched instruction and operands are
obtained from the retained compiler certificate. The postcondition preserves
the continuation certificate at the actual incremented program counter. -/
namespace Exec.Interp
open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem step_eqz_certified
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (next : Nat) (output : List valtype) (s : _root_.store) (ambient : frame) (f : Abs.AFrame)
    (rest : List Abs.AFrame) (after : List instr) (front : List val) (ty : Inn) (a : Nat)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some code)
    (pcBound : raw.pc.val < U32.max)
    (ha : a < 2 ^ Abs.integerWidth ty)
    (typed : Abs.ATyped ⟨s, ambient, { f with
      code := .TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ) :: after,
      vals := front ++ [Abs.integerVal ty a] } :: rest, []⟩)
    (slots : FrameSlots exec raw { f with vals := front ++ [Abs.integerVal ty a] })
    (point : LinearPoint raw { f with
      code := .TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ) :: after,
      vals := front ++ [Abs.integerVal ty a] } code next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧
      FrameSlots out.2.1 raw { f with code := after, vals := front ++ [Abs.integerVal .I32 (if a = 0 then 1 else 0)] } ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      (∃ pc : U32, pc.val = raw.pc.val + 1 ∧
        { out.2.1 with slots := exec.slots } =
          { exec with frames := exec.frames.set index { raw with pc := pc } } ∧
        LinearPoint { raw with pc := pc }
          { f with code := after, vals := front ++ [Abs.integerVal .I32 (if a = 0 then 1 else 0)] }
          code next output) ∧
      Abs.NextSim
        ⟨s, ambient, { f with code := .TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ) :: after, vals := front ++ [Abs.integerVal ty a] } :: rest, []⟩
        ⟨s, ambient, { f with code := after, vals := front ++ [Abs.integerVal .I32 (if a = 0 then 1 else 0)] } :: rest, []⟩ ⦄ := by
  obtain ⟨slot, position, fetched, continuation⟩ := linearPoint_eqz front ty a after point
  apply WP.spec_mono (step_eqz_refines memory hooks floats allocator
    exec store platform index raw inst code slot s ambient f rest after front ty a
    last hf hi hc fetched pcBound ha typed slots position)
  intro out effect
  obtain ⟨success, represented, sameStore, samePlatform, ⟨pc, hpc, unchanged⟩, simulation⟩ := effect
  refine ⟨success, represented, sameStore, samePlatform, ⟨pc, hpc, unchanged, ?_⟩, simulation⟩
  simpa only [LinearPoint, hpc] using continuation

end Exec.Interp
