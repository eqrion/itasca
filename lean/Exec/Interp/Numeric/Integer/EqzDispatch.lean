import Exec.Interp.Numeric.Integer.Eqz
import Exec.Interp.Relations.Fetch

/-! Compose the extracted dispatch and checked instruction fetch with local
value refinement. Store and platform equality are explicit for pure scalar
instructions; the handler relation alone does not hide those effects. -/
namespace Exec.Interp
open Aeneas Aeneas.Std

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

def eqzInstruction (ty : Inn) (slot : U32) : Code.Bytecode :=
  if ty = .I32 then .I32Eqz slot slot slot else .I64Eqz slot slot slot

theorem dispatch_eqz_eq (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (index inst function base : Usize)
    (ty : Inn) (slot : U32) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index inst function base
      (eqzInstruction ty slot) = (do
        let (r, next) ← runtime.interp.execute_scalar floats exec base
          (if ty = .I32 then 69#u16 else 80#u16) slot slot slot
        Result.ok (r, next, store, platform)) := by
  cases ty <;> simp only [eqzInstruction, reduceCtorEq, ite_true, ite_false] <;>
    simp only [runtime.interp.dispatch, runtime.interp.dispatch_scalar,
      runtime.interp.scalar_operands, bind_ok] <;> rfl

theorem dispatch_eqz {Q : core.result.Result Unit runtime.ExecError × runtime.interp.Execution → Prop}
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index inst function base : Usize) (ty : Inn) (slot : U32)
    (handler : runtime.interp.execute_scalar floats exec base
      (if ty = .I32 then 69#u16 else 80#u16) slot slot slot ⦃ Q ⦄) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index inst function base
      (eqzInstruction ty slot) ⦃ out =>
        Q (out.1, out.2.1) ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ⦄ := by
  rw [dispatch_eqz_eq]
  obtain ⟨out, result, property⟩ := WP.spec_imp_exists handler
  rw [result]
  rcases out with ⟨r, next⟩
  simp only [bind_ok]
  with_unfolding_all apply WP.spec.ret
  exact ⟨property, rfl, rfl⟩

/-- A complete extracted interpreter iteration for integer zero testing. The
concrete fetch premises name the actual retained instruction and owning
instance; typed abstract operands supply the source reduction. -/
theorem step_eqz_refines
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (slot : U32) (s : _root_.store) (ambient : frame) (f : Abs.AFrame)
    (rest : List Abs.AFrame) (after : List instr) (front : List val) (ty : Inn) (a : Nat)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some code)
    (hop : code.code.val[raw.pc.val]? = some (eqzInstruction ty slot))
    (pcBound : raw.pc.val < U32.max)
    (ha : a < 2 ^ Abs.integerWidth ty)
    (typed : Abs.ATyped ⟨s, ambient, { f with
      code := .TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ) :: after,
      vals := front ++ [Abs.integerVal ty a] } :: rest, []⟩)
    (slots : FrameSlots exec raw { f with vals := front ++ [Abs.integerVal ty a] })
    (position : slot.val = Code.slots ((f.locals ++ front).map Code.valueType)) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧
      FrameSlots out.2.1 raw { f with code := after, vals := front ++ [Abs.integerVal .I32 (if a = 0 then 1 else 0)] } ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      (∃ pc : U32, pc.val = raw.pc.val + 1 ∧
        { out.2.1 with slots := exec.slots } =
          { exec with frames := exec.frames.set index { raw with pc := pc } }) ∧
      Abs.NextSim
        ⟨s, ambient, { f with code := .TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ) :: after, vals := front ++ [Abs.integerVal ty a] } :: rest, []⟩
        ⟨s, ambient, { f with code := after, vals := front ++ [Abs.integerVal .I32 (if a = 0 then 1 else 0)] } :: rest, []⟩ ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform index raw inst code
    (eqzInstruction ty slot) last hf hi hc hop pcBound
  intro pc hpc
  have handler := integer_eqz_refines floats
    { exec with frames := exec.frames.set index { raw with pc := pc } }
    raw slot s ambient f rest after front ty a ha typed slots position
  apply WP.spec_mono (dispatch_eqz memory hooks floats allocator
    { exec with frames := exec.frames.set index { raw with pc := pc } }
    store platform index raw.instance raw.function raw.base ty slot handler)
  intro out effect
  obtain ⟨⟨success, represented, unchanged, simulation⟩, sameStore, samePlatform⟩ := effect
  exact ⟨success, represented, sameStore, samePlatform, ⟨pc, hpc, unchanged⟩, simulation⟩

end Exec.Interp
