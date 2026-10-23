import Exec.Interp.Machines.Slice.SliceDispatch
import Exec.Interp.Machines.Slice.SliceCodePoint

/-! A complete concrete iteration whose fetched instruction and operands are
obtained from the retained compiler certificate. The postcondition preserves
the continuation certificate at the actual incremented program counter. -/
namespace Exec.Interp
open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem step_sliceBinary_certified
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (next : Nat) (output : List valtype) (s : _root_.store) (ambient : frame) (f : Abs.AFrame)
    (rest : List Abs.AFrame) (after : List instr) (front : List val) (ty : Inn) (op : SliceBinary) (a b : Nat)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some code)
    (pcBound : raw.pc.val < U32.max)
    (ha : a < 2 ^ Abs.integerWidth ty) (hb : b < 2 ^ Abs.integerWidth ty)
    (typed : Abs.ATyped ⟨s, ambient, { f with
      code := (op.operation.source ty) :: after,
      vals := front ++ [Abs.integerVal ty a, Abs.integerVal ty b] } :: rest, []⟩)
    (slots : FrameSlots exec raw { f with vals := front ++ [Abs.integerVal ty a, Abs.integerVal ty b] })
    (point : LinearPoint raw { f with
      code := (op.operation.source ty) :: after,
      vals := front ++ [Abs.integerVal ty a, Abs.integerVal ty b] } code next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧
      FrameSlots out.2.1 raw { f with code := after, vals := front ++ [Abs.integerVal (op.resultType ty) (op.result ty a b)] } ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      (∃ pc : U32, pc.val = raw.pc.val + 1 ∧
        { out.2.1 with slots := exec.slots } =
          { exec with frames := exec.frames.set index { raw with pc := pc } } ∧
        LinearPoint { raw with pc := pc }
          { f with code := after, vals := front ++ [Abs.integerVal (op.resultType ty) (op.result ty a b)] }
          code next output) ∧
      Abs.NextSim
        ⟨s, ambient, { f with code := (op.operation.source ty) :: after, vals := front ++ [Abs.integerVal ty a, Abs.integerVal ty b] } :: rest, []⟩
        ⟨s, ambient, { f with code := after, vals := front ++ [Abs.integerVal (op.resultType ty) (op.result ty a b)] } :: rest, []⟩ ⦄ := by
  obtain ⟨left, right, hl, hr, fetched, continuation⟩ := linearPoint_slice front ty op a b after point
  have hr' : right.val = Code.slots ((f.locals ++ front).map Code.valueType) + 1 := by omega
  apply WP.spec_mono (step_sliceBinary_refines memory hooks floats allocator
    exec store platform index raw inst code left right s ambient f rest after front ty op a b
    last hf hi hc fetched pcBound ha hb typed slots hl hr')
  intro out effect
  obtain ⟨success, represented, sameStore, samePlatform, ⟨pc, hpc, unchanged⟩, simulation⟩ := effect
  refine ⟨success, represented, sameStore, samePlatform, ⟨pc, hpc, unchanged, ?_⟩, simulation⟩
  simpa only [LinearPoint, hpc] using continuation

end Exec.Interp
