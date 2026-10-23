import Exec.Interp.Relations.InitializerExecute
import Exec.Code.Local.Initializer.Initializer
import Exec.Interp.Relations.Ensure
import Exec.Interp.Control.LoopBasis

/-! Read-only synthetic initializer execution. `InitialRead` records only the
instruction shape, literal bits, and resolved store addresses. It contains no
interpreter execution premise. -/
namespace Exec.Interp
open Aeneas Aeneas.Std

inductive InitialRead {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction) :
    runtime.bytecode.Instr → List U64 → Prop where
  | const32 (bits : U32) : InitialRead store inst code (.Const32 0#u32 bits)
      [UScalar.cast .U64 bits]
  | const64 (bits : U64) : InitialRead store inst code (.Const64 0#u32 bits) [bits]
  | vector (pool : U32) (bits : U128) (hpool : code.v128_pool.val[pool.val]? = some bits) :
      InitialRead store inst code (.ConstV128 0#u32 pool)
        [UScalar.cast .U64 bits, UScalar.cast .U64 (⟨bits.bv >>> 64⟩ : U128)]
  | null : InitialRead store inst code (.RefNull 0#u32) [0#u64]
  | func (index : U32) (addr : runtime.FuncAddr) (reference : U64)
      (lookup : inst.funcs.val[index.val]? = some addr)
      (encoded : reference.val = addr.index.val + 1) :
      InitialRead store inst code (.RefFunc 0#u32 index) [reference]
  | global (index : U32) (addr : runtime.GlobalAddr) (value : runtime.store.GlobalInst)
      (lookup : inst.globals.val[index.val]? = some addr)
      (resolved : store.globals.val[addr.index.val]? = some value) :
      InitialRead store inst code (.GlobalGet 0#u32 index) [value.lo]
  | global2 (index : U32) (addr : runtime.GlobalAddr) (value : runtime.store.GlobalInst)
      (lookup : inst.globals.val[index.val]? = some addr)
      (resolved : store.globals.val[addr.index.val]? = some value) :
      InitialRead store inst code (.GlobalGet2 0#u32 index) [value.lo, value.hi]

def initialSlots (before words : List U64) : List U64 :=
  match words with
  | [lo] => before.set 0 lo
  | [lo, hi] => (before.set 0 lo).set 1 hi
  | _ => before

theorem initialSlots_length (before words : List U64) :
    (initialSlots before words).length = before.length := by
  unfold initialSlots
  split <;> simp_all

theorem InitialRead.width {M : Type} {store : runtime.store.Store M}
    {inst code instruction words} (read : InitialRead store inst code instruction words) :
    words.length = 1 ∨ words.length = 2 := by cases read <;> simp

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem dispatch_initial_read (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (instIndex function frameIndex : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) (words : List U64)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hc : inst.module.functions.val[function.val]? = some code)
    (read : InitialRead store inst code instruction words)
    (capacity : words.length ≤ exec.slots.length) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex
      instIndex function 0#usize instruction ⦃ out =>
        out.1 = .Ok () ∧ SlotsEffect exec out.2.1 (initialSlots exec.slots.val words) ∧
        out.2.2.1 = store ∧ out.2.2.2 = platform ⦄ := by
  cases read with
  | const32 bits =>
    simp only [runtime.interp.dispatch]
    step with const32_effect exec 0#usize 0#u32 bits (by simp only [List.length_cons, List.length_nil] at capacity; scalar_tac)
    simp_all [initialSlots]
  | const64 bits =>
    simp only [runtime.interp.dispatch]
    step with const64_effect exec 0#usize 0#u32 bits (by simp only [List.length_cons, List.length_nil] at capacity; scalar_tac)
    simp_all [initialSlots]
  | vector pool bits hpool =>
    simp only [runtime.interp.dispatch]
    step with const_v128_effect memory exec store instIndex function
      0#usize 0#u32 pool inst code bits hi hc hpool (by simp only [List.length_cons, List.length_nil] at capacity; scalar_tac)
    simp_all [initialSlots]
  | null =>
    simp only [runtime.interp.dispatch]
    step with ref_null_effect exec 0#usize 0#u32 (by simp only [List.length_cons, List.length_nil] at capacity; scalar_tac)
    simp_all [initialSlots]
  | func index addr reference lookup encoded =>
    simp only [runtime.interp.dispatch]
    have bound : addr.index.val < U64.max := by scalar_tac
    step with ref_func_effect memory exec store instIndex 0#usize 0#u32
      index inst addr hi lookup bound (by simp only [List.length_cons, List.length_nil] at capacity; scalar_tac)
      as ⟨result, after, store', hok, hs, actual, hactual, heffect⟩
    have heq : actual = reference := by scalar_tac
    simp_all [initialSlots]
  | global index addr value lookup resolved =>
    simp only [runtime.interp.dispatch]
    step with global_get_effect memory exec store instIndex 0#usize
      0#u32 index inst addr value hi lookup resolved (by simp only [List.length_cons, List.length_nil] at capacity; scalar_tac)
    simp_all [initialSlots]
  | global2 index addr value lookup resolved =>
    simp only [runtime.interp.dispatch]
    step with global_get2_effect memory exec store instIndex 0#usize
      0#u32 index inst addr value hi lookup resolved (by simp only [List.length_cons, List.length_nil] at capacity; scalar_tac)
    simp_all [initialSlots]

/-- Exact frame used by a retained initializer. It owns no caller frame and
starts at absolute slot zero. -/
def initializerFrame (instIndex function : Usize) (pc : U32) : runtime.interp.Frame :=
  { «instance» := instIndex, function := function, pc := pc, base := 0#usize }

theorem step_initial_read (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) (words : List U64)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hc : inst.module.functions.val[function.val]? = some code)
    (read : InitialRead store inst code instruction words)
    (capacity : words.length ≤ exec.slots.length)
    (hf : exec.frames.val = [initializerFrame instIndex function 0#u32])
    (hop : code.code.val[0]? = some instruction) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.1.slots.val = initialSlots exec.slots.val words ∧
      out.2.1.frames.val = [initializerFrame instIndex function 1#u32] ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform 0#usize
    (initializerFrame instIndex function 0#u32) inst code instruction
    (by simpa [alloc.vec.Vec.length, hf]) (by simp [hf]) hi hc hop (by simp [initializerFrame, U32.max_eq])
  intro pc hpc
  have heq : pc = 1#u32 := by simp only [initializerFrame] at hpc; scalar_tac
  subst pc
  apply WP.spec_mono (dispatch_initial_read memory hooks floats allocator
    { exec with frames := exec.frames.set 0#usize (initializerFrame instIndex function 1#u32) }
    store platform instIndex function 0#usize inst code instruction words hi hc read capacity)
  rintro out ⟨hok, ⟨hslots, hrest⟩, hs, hp⟩
  have hframes := congrArg runtime.interp.Execution.frames hrest
  exact ⟨hok, hslots, by simpa [hf] using congrArg alloc.vec.Vec.val hframes, hs, hp⟩

theorem step_initial_return (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction) (width : U32)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hc : inst.module.functions.val[function.val]? = some code)
    (capacity : width.val ≤ exec.slots.length)
    (hf : exec.frames.val = [initializerFrame instIndex function 1#u32])
    (hop : code.code.val[1]? = some (.Return 0#u32 width)) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.1.slots = exec.slots ∧ out.2.1.frames.val = [] ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform 0#usize
    (initializerFrame instIndex function 1#u32) inst code (.Return 0#u32 width)
    (by simpa [alloc.vec.Vec.length, hf]) (by simp [hf]) hi hc hop (by simp [initializerFrame, U32.max_eq])
  intro pc hpc
  simp only [runtime.interp.dispatch, initializerFrame]
  step with initializer_return_effect
    { exec with frames := exec.frames.set 0#usize { «instance» := instIndex, function := function, pc := pc, base := 0#usize } }
    width capacity
  simp_all [hf]

/-- The extracted loop body continues exactly when its singleton frame takes
one normally returning instruction. -/
theorem synthetic_body_active (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P)
    (active : 0 < exec.frames.length) :
    runtime.interp.run_synthetic_loop.body memory hooks floats allocator store platform exec (.Ok ()) =
      (do let (status, next, store', platform') ←
            runtime.interp.step memory hooks floats allocator exec store platform
          .ok (.cont (store', platform', next, status))) := by
  have nonempty : exec.frames.val ≠ [] := by intro h; simp [alloc.vec.Vec.length, h] at active
  simp [runtime.interp.run_synthetic_loop.body, core.result.Result.is_ok, nonempty]

theorem synthetic_body_done (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P)
    (empty : exec.frames.val = []) :
    runtime.interp.run_synthetic_loop.body memory hooks floats allocator store platform exec (.Ok ()) =
      .ok (.done (store, platform, exec.slots, .Ok ())) := by
  simp [runtime.interp.run_synthetic_loop.body, alloc.vec.Vec.len, empty]

end Exec.Interp
