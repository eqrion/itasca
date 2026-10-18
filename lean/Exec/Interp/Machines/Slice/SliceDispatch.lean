import Exec.Interp.Machines.Slice.SliceBinary
import Exec.Interp.Relations.Fetch

/-! Compose the extracted dispatch and checked instruction fetch with local
value refinement. Store and platform equality are explicit for pure scalar
instructions; the handler relation alone does not hide those effects. -/
namespace Exec.Interp
open Aeneas Aeneas.Std

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem dispatch_sliceBinary_eq (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (index inst function base : Usize)
    (ty : Inn) (op : SliceBinary) (left right : U32) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index inst function base
      (Code.IntegerBinary.target ty op.operation left right) = (do
        let (r, next) ← runtime.interp.execute_scalar floats exec base
          (op.opcode ty) left left right
        Result.ok (r, next, store, platform)) := by
  cases op <;> cases ty <;> simp [SliceBinary.opcode, SliceBinary.operation,
    Code.IntegerBinary.target, runtime.interp.dispatch,
    runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]

theorem dispatch_sliceBinary {Q : core.result.Result Unit runtime.ExecError × runtime.interp.Execution → Prop}
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index inst function base : Usize) (ty : Inn) (op : SliceBinary) (left right : U32)
    (handler : runtime.interp.execute_scalar floats exec base
      (op.opcode ty) left left right ⦃ Q ⦄) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index inst function base
      (Code.IntegerBinary.target ty op.operation left right) ⦃ out =>
        Q (out.1, out.2.1) ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ⦄ := by
  rw [dispatch_sliceBinary_eq]
  obtain ⟨out, result, property⟩ := WP.spec_imp_exists handler
  rw [result]
  rcases out with ⟨r, next⟩
  simp only [bind_ok]
  with_unfolding_all apply WP.spec.ret
  exact ⟨property, rfl, rfl⟩

/-- A complete extracted interpreter iteration for integer addition. The
concrete fetch premises name the actual retained instruction and owning
instance; typed abstract operands supply the source reduction. -/
theorem step_sliceBinary_refines
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.Instance) (code : runtime.bytecode.CompiledFunction)
    (left right : U32) (s : _root_.store) (ambient : frame) (f : Abs.AFrame)
    (rest : List Abs.AFrame) (after : List instr) (front : List val) (ty : Inn) (op : SliceBinary) (a b : Nat)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some code)
    (hop : code.code.val[raw.pc.val]? = some (Code.IntegerBinary.target ty op.operation left right))
    (pcBound : raw.pc.val < U32.max)
    (ha : a < 2 ^ Abs.integerWidth ty) (hb : b < 2 ^ Abs.integerWidth ty)
    (typed : Abs.ATyped ⟨s, ambient, { f with
      code := (op.operation.source ty) :: after,
      vals := front ++ [Abs.integerVal ty a, Abs.integerVal ty b] } :: rest, []⟩)
    (slots : FrameSlots exec raw { f with vals := front ++ [Abs.integerVal ty a, Abs.integerVal ty b] })
    (hleft : left.val = Code.slots ((f.locals ++ front).map Code.valueType))
    (hright : right.val = Code.slots ((f.locals ++ front).map Code.valueType) + 1) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧
      FrameSlots out.2.1 raw { f with code := after, vals := front ++ [Abs.integerVal (op.resultType ty) (op.result ty a b)] } ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      (∃ pc : U32, pc.val = raw.pc.val + 1 ∧
        { out.2.1 with slots := exec.slots } =
          { exec with frames := exec.frames.set index { raw with pc := pc } }) ∧
      Abs.NextSim
        ⟨s, ambient, { f with code := (op.operation.source ty) :: after, vals := front ++ [Abs.integerVal ty a, Abs.integerVal ty b] } :: rest, []⟩
        ⟨s, ambient, { f with code := after, vals := front ++ [Abs.integerVal (op.resultType ty) (op.result ty a b)] } :: rest, []⟩ ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform index raw inst code
    (Code.IntegerBinary.target ty op.operation left right) last hf hi hc hop pcBound
  intro pc hpc
  have handler := sliceBinary_refines floats
    { exec with frames := exec.frames.set index { raw with pc := pc } }
    raw left right s ambient f rest after front ty op a b ha hb typed slots hleft hright
  apply WP.spec_mono (dispatch_sliceBinary memory hooks floats allocator
    { exec with frames := exec.frames.set index { raw with pc := pc } }
    store platform index raw.instance raw.function raw.base ty op left right handler)
  intro out effect
  obtain ⟨⟨success, represented, unchanged, simulation⟩, sameStore, samePlatform⟩ := effect
  exact ⟨success, represented, sameStore, samePlatform, ⟨pc, hpc, unchanged⟩, simulation⟩

end Exec.Interp
