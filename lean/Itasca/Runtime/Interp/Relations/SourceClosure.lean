import Itasca.Runtime.Interp.Relations.Defaults
import Itasca.Runtime.Compiler.Local.Initializer
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.SourceMachine.Sim.Structured
import Itasca.Runtime.SourceMachine.CallSafety
import Itasca.Runtime.SourceMachine.Numeric.Decode
import Itasca.Runtime.SourceMachine.Sim.Host
import Itasca.Runtime.SourceMachine.Bound
import Itasca.Runtime.SourceMachine.BrTable

/-!
Sections, each formerly its own module: InitializerExecute, Initializer, Synthetic, InitializerResolution, Range, ControlEntry, Erased, SourceClosure.
-/

/-! ## InitializerExecute -/

section

/-! Exact effects of the read-only instruction handlers used by retained
constant-initializer functions. Store lookups are explicit premises, independent
of any execution-correctness certificate. -/
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

@[step] theorem ref_null_effect (exec : runtime.interp.Execution)
    (base : Usize) (dst : U32) (hd : base.val + dst.val < exec.slots.length) :
    runtime.interp.execute_ref_null exec base dst
      ⦃ out => out.1 = .Ok () ∧ SlotsEffect exec out.2
        (exec.slots.val.set (base.val + dst.val) 0#u64) ⦄ := by
  unfold runtime.interp.execute_ref_null
  step* <;> simp_all [SlotsEffect]

@[step] theorem global_get_effect (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (instIndex : Usize) (base : Usize) (dst global : U32)
    (inst : runtime.store.ModuleInst) (addr : runtime.GlobalAddr) (value : runtime.store.GlobalInst)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (ha : inst.globals.val[global.val]? = some addr)
    (hv : store.globals.val[addr.index.val]? = some value)
    (hd : base.val + dst.val < exec.slots.length) :
    runtime.interp.execute_global_get memory exec store instIndex base dst global
      ⦃ out => out.1 = .Ok () ∧ out.2.2 = store ∧ SlotsEffect exec out.2.1
        (exec.slots.val.set (base.val + dst.val) value.lo) ⦄ := by
  unfold runtime.interp.execute_global_get
  step with vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
  subst found
  simp only [lift, bind_ok]
  step with vec_index_given inst.globals (UScalar.cast .Usize global) addr (by simpa using ha) as ⟨found, hfound⟩
  subst found
  step with vec_index_given store.globals addr.index value hv as ⟨found, hfound⟩
  subst found
  step* <;> simp_all [SlotsEffect]

@[step] theorem global_get2_effect (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (instIndex : Usize) (base : Usize) (dst global : U32)
    (inst : runtime.store.ModuleInst) (addr : runtime.GlobalAddr) (value : runtime.store.GlobalInst)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (ha : inst.globals.val[global.val]? = some addr)
    (hv : store.globals.val[addr.index.val]? = some value)
    (hd : base.val + dst.val + 1 < exec.slots.length) :
    runtime.interp.execute_global_get2 memory exec store instIndex base dst global
      ⦃ out => out.1 = .Ok () ∧ out.2.2 = store ∧ SlotsEffect exec out.2.1
        ((exec.slots.val.set (base.val + dst.val) value.lo).set (base.val + dst.val + 1) value.hi) ⦄ := by
  unfold runtime.interp.execute_global_get2
  step with vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
  subst found
  simp only [lift, bind_ok]
  step with vec_index_given inst.globals (UScalar.cast .Usize global) addr (by simpa using ha) as ⟨found, hfound⟩
  subst found
  step with vec_index_given store.globals addr.index value hv as ⟨found, hfound⟩
  subst found
  step* <;> simp_all [SlotsEffect]

@[step] theorem const_v128_effect (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (instIndex function base : Usize) (dst pool : U32)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction) (value : U128)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hc : inst.module.functions.val[function.val]? = some code)
    (hv : code.v128_pool.val[pool.val]? = some value)
    (hd : base.val + dst.val + 1 < exec.slots.length) :
    runtime.interp.execute_const_v128 memory exec store instIndex function base dst pool
      ⦃ out => out.1 = .Ok () ∧ out.2.2 = store ∧ SlotsEffect exec out.2.1
        ((exec.slots.val.set (base.val + dst.val) (UScalar.cast .U64 value)).set
          (base.val + dst.val + 1) (UScalar.cast .U64 (⟨value.bv >>> 64⟩ : U128))) ⦄ := by
  unfold runtime.interp.execute_const_v128
  step with vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
  subst found
  step with vec_index_given inst.module.functions function code hc as ⟨found, hfound⟩
  subst found
  simp only [lift, bind_ok]
  step with vec_index_given code.v128_pool (UScalar.cast .Usize pool) value (by simpa using hv) as ⟨found, hfound⟩
  subst found
  step* <;> simp_all [SlotsEffect]
  congr 2
  apply U128.bv_eq_imp_eq
  assumption

@[step] theorem ref_func_effect (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (instIndex base : Usize) (dst func : U32)
    (inst : runtime.store.ModuleInst) (addr : runtime.FuncAddr)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (ha : inst.funcs.val[func.val]? = some addr)
    (href : addr.index.val < U64.max)
    (hd : base.val + dst.val < exec.slots.length) :
    runtime.interp.execute_ref_func memory exec store instIndex base dst func
      ⦃ out => out.1 = .Ok () ∧ out.2.2 = store ∧ ∃ reference : U64,
        reference.val = addr.index.val + 1 ∧ SlotsEffect exec out.2.1
          (exec.slots.val.set (base.val + dst.val) reference) ⦄ := by
  unfold runtime.interp.execute_ref_func
  step with vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
  subst found
  simp only [lift, bind_ok]
  step with vec_index_given inst.funcs (UScalar.cast .Usize func) addr (by simpa using ha)
    as ⟨found, hfound⟩
  subst found
  have hchecked := U64.checked_add_bv_spec (UScalar.cast .U64 addr.index) 1#u64
  have hcast : (UScalar.cast .U64 addr.index).val = addr.index.val := by
    have hb : addr.index.val < 2^64 := lt_trans href (by simp [U64.max_eq])
    simp [UScalar.cast_val_eq, UScalarTy.numBits]
    exact hb
  cases hnext : U64.checked_add (UScalar.cast .U64 addr.index) 1#u64 with
  | none =>
    simp only [hnext] at hchecked
    scalar_tac
  | some reference =>
    simp only [hnext] at hchecked ⊢
    step* <;> simp_all [SlotsEffect]
    exact ⟨reference, by scalar_tac, rfl⟩

theorem copy_words_self (words : List U64) (src n : Nat) (h : src + n ≤ words.length) :
    copyWords words src src n = words := by
  induction n generalizing src with
  | zero => rfl
  | succ n ih =>
    have hs : src < words.length := by omega
    simp only [copyWords]
    rw [show words.set src words[src]! = words by simp [hs]]
    exact ih (src + 1) (by omega)

@[step] theorem initializer_return_effect (exec : runtime.interp.Execution)
    (width : U32) (hwidth : width.val ≤ exec.slots.length) :
    runtime.interp.execute_return exec 0#usize 0#u32 width
      ⦃ out => out.1 = .Ok () ∧ out.2.slots = exec.slots ∧
        out.2.frames.val = exec.frames.val.dropLast ∧
        { out.2 with frames := exec.frames } = exec ⦄ := by
  apply WP.spec_mono (return_effect exec 0#usize 0#u32 width
    (by simpa using hwidth) (by scalar_tac))
  rintro out ⟨hok, hslots, hframes, hrest⟩
  have he : out.2.slots = exec.slots := by
    apply alloc.vec.Vec.ext
    simpa [copy_words_self exec.slots.val 0 width.val (by simpa using hwidth)] using hslots
  exact ⟨hok, he, hframes, by simpa [he] using hrest⟩

end Itasca.Runtime.Interp

end

/-! ## Initializer -/

section

/-! Read-only synthetic initializer execution. `InitialRead` records only the
instruction shape, literal bits, and resolved store addresses. It contains no
interpreter execution premise. -/
namespace Itasca.Runtime.Interp
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

theorem initial_slots_length (before words : List U64) :
    (initialSlots before words).length = before.length := by
  unfold initialSlots
  split <;> simp_all

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

end Itasca.Runtime.Interp

end

/-! ## Synthetic -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem synthetic_loop_initializer (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) (words : List U64) (width : U32)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hc : inst.module.functions.val[function.val]? = some code)
    (read : InitialRead store inst code instruction words)
    (capacity : words.length ≤ exec.slots.length)
    (returnCapacity : width.val ≤ exec.slots.length)
    (hf : exec.frames.val = [initializerFrame instIndex function 0#u32])
    (hcode : code.code.val = [instruction, .Return 0#u32 width]) :
    runtime.interp.run_synthetic_loop memory hooks floats allocator store platform exec (.Ok ())
      ⦃ out => out.1 = store ∧ out.2.1 = platform ∧
        out.2.2.1.val = initialSlots exec.slots.val words ∧ out.2.2.2 = .Ok () ⦄ := by
  obtain ⟨⟨status1, exec1, store1, platform1⟩, first, hok1, slots1, frames1, hs1, hp1⟩ :=
    WP.spec_imp_exists (step_initial_read memory hooks floats allocator exec store platform
      instIndex function inst code instruction words hi hc read capacity hf (by simp [hcode]))
  dsimp only at hok1 slots1 frames1 hs1 hp1
  subst status1 store1 platform1
  have capacity1 : width.val ≤ exec1.slots.length := by
    change width.val ≤ exec1.slots.val.length
    rw [slots1, initial_slots_length]
    exact returnCapacity
  obtain ⟨⟨status2, exec2, store2, platform2⟩, second, hok2, slots2, frames2, hs2, hp2⟩ :=
    WP.spec_imp_exists (step_initial_return memory hooks floats allocator exec1 store platform
      instIndex function inst code width hi hc capacity1 frames1 (by simp [hcode]))
  dsimp only at hok2 slots2 frames2 hs2 hp2
  subst status2 store2 platform2
  have active0 : 0 < exec.frames.length := by simp [alloc.vec.Vec.length, hf]
  have active1 : 0 < exec1.frames.length := by simp [alloc.vec.Vec.length, frames1]
  have body0 := synthetic_body_active memory hooks floats allocator exec store platform active0
  have body1 := synthetic_body_active memory hooks floats allocator exec1 store platform active1
  rw [first, bind_ok] at body0
  rw [second, bind_ok] at body1
  have body2 := synthetic_body_done memory hooks floats allocator exec2 store platform frames2
  have trace : NormalTrace (fun state : runtime.store.Store M × P × runtime.interp.Execution ×
      core.result.Result Unit runtime.ExecError =>
      runtime.interp.run_synthetic_loop.body memory hooks floats allocator state.1 state.2.1
        state.2.2.1 state.2.2.2) 2
      (store, platform, exec, .Ok ()) (store, platform, exec2.slots, .Ok ()) :=
    .next body0 (.next body1 (.done body2))
  change loop _ _ ⦃ _ ⦄
  rw [trace.result]
  simp [WP.spec_ok, slots2, slots1]

@[step] theorem get_effect (slots : Slice U64) (position : Usize) :
    runtime.interp.get slots position ⦃ value =>
      value = (slots.val[position.val]?).getD 0#u64 ⦄ := by
  unfold runtime.interp.get
  dsimp only
  split
  · rename_i inside
    step as ⟨value, hvalue⟩
    have bound : position.val < slots.val.length := by scalar_tac
    simp [List.getElem?_eq_getElem bound, hvalue]
  · rename_i outside
    have bound : slots.val.length ≤ position.val := by scalar_tac
    simp [List.getElem?_eq_none bound]

theorem InitialRead.zero_slots {store : runtime.store.Store M} {inst code instruction words}
    (read : InitialRead store inst code instruction words) :
    initialSlots (List.replicate words.length 0#u64) words = words := by
  cases read <;> simp [initialSlots]

/-- The complete extracted synthetic entry point terminates for a resolved
constant initializer. Allocation failure is permitted; every result preserves
the raw Store and platform exactly. Successful results are the resolved words. -/
theorem synthetic_initializer (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) (words : List U64)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hc : inst.module.functions.val[function.val]? = some code)
    (read : InitialRead store inst code instruction words)
    (width : code.slot_count.val = words.length)
    (hcode : code.code.val = [instruction, .Return 0#u32 code.slot_count]) :
    runtime.interp.run_synthetic memory hooks floats allocator store platform instIndex function
      ⦃ out => out.2.1 = store ∧ out.2.2 = platform ∧
        ∀ pair, out.1 = .Ok pair → pair = ((words[0]?).getD 0#u64, (words[1]?).getD 0#u64) ⦄ := by
  unfold runtime.interp.run_synthetic
  step with vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
  subst found
  step with vec_index_given inst.module.functions function code hc as ⟨found, hfound⟩
  subst found
  simp only [lift, bind_ok, runtime.interp.Execution.new]
  step with ensure_effect allocator law _ _ _ as ⟨status, prepared, ensured⟩
  cases status with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok unit =>
    cases unit
    simp only [EnsureEffect] at ensured
    obtain ⟨limit, hslots, hother⟩ := ensured
    have slots : prepared.slots.val = List.replicate words.length 0#u64 := by
      simpa [alloc.vec.Vec.new, width] using hslots
    have frames : prepared.frames.val = [] := by
      have h := congrArg runtime.interp.Execution.frames hother
      simpa [alloc.vec.Vec.new] using congrArg alloc.vec.Vec.val h
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨answer, reserved⟩ := law.reserve_eq prepared.frames 1#usize
    have reserveCall : runtime.reserve allocator prepared.frames 1#usize = .ok
        ((if answer then .Ok () else .Err (.Exhausted .Allocation)), prepared.frames) := by
      cases answer <;> simp [runtime.reserve, reserved]
    rw [reserveCall, bind_ok]
    cases answer with
    | false =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | true =>
      simp only [↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step as ⟨pushed, hpushed⟩
      have pushedFrames : pushed.val = [initializerFrame instIndex function 0#u32] := by
        simpa [frames, initializerFrame] using hpushed
      have capacity : words.length ≤ prepared.slots.length := by
        simp [alloc.vec.Vec.length, slots]
      step with synthetic_loop_initializer memory hooks floats allocator
        { prepared with frames := pushed } store platform instIndex function inst code instruction words
        code.slot_count hi hc read capacity (by simpa [width] using capacity) pushedFrames hcode
        as ⟨store', platform', finalSlots, result, hs, hp, hwords, hok⟩
      subst store' platform' result
      have finalWords : finalSlots.val = words := by
        rw [slots, read.zero_slots] at hwords
        exact hwords
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with get_effect finalSlots.deref 0#usize as ⟨lo, hlo⟩
      step with get_effect finalSlots.deref 1#usize as ⟨hi, hhi⟩
      have low : lo = (words[0]?).getD 0#u64 := by simpa [alloc.vec.Vec.deref, finalWords] using hlo
      have high : hi = (words[1]?).getD 0#u64 := by simpa [alloc.vec.Vec.deref, finalWords] using hhi
      simp [low, high]

end Itasca.Runtime.Interp

end

/-! ## InitializerResolution -/

section

/-! Resolve retained initializer certificates against concrete instance maps.
The resolution relation describes source literals and store reads only; the
machine theorem is derived from it and the compiler's syntactic certificate. -/
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem initializer_bits_low (lo hi : U64) :
    UScalar.cast .U64 (Compiler.initializerBits lo hi) = lo := by
  apply U64.bv_eq_imp_eq
  simp only [Compiler.initializerBits, UScalar.cast_bv_eq]
  apply BitVec.eq_of_getLsbD_eq
  intro i h
  change i < 64 at h
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  simp [h, show i < 128 by omega, show ¬64 ≤ i by omega]

theorem initializer_bits_high (lo hi : U64) :
    UScalar.cast .U64 (⟨(Compiler.initializerBits lo hi).bv >>> 64⟩ : U128) = hi := by
  apply U64.bv_eq_imp_eq
  simp only [Compiler.initializerBits, UScalar.cast_bv_eq]
  apply BitVec.eq_of_getLsbD_eq
  intro i h
  change i < 64 at h
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  simp [h, show 64 + i < 128 by omega, show i < 128 by omega]

inductive InitializerResolution {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) :
    Itasca.wasm_types.ConstExpr → Itasca.wasm_types.ValueType → List U64 → Prop where
  | i32 (value : I32) : InitializerResolution store inst (.I32 value) .I32
      [UScalar.cast .U64 (IScalar.hcast .U32 value)]
  | i64 (value : I64) : InitializerResolution store inst (.I64 value) .I64
      [IScalar.hcast .U64 value]
  | f32 (bits : U32) : InitializerResolution store inst (.F32 bits) .F32 [UScalar.cast .U64 bits]
  | f64 (bits : U64) : InitializerResolution store inst (.F64 bits) .F64 [bits]
  | vector (lo hi : U64) : InitializerResolution store inst (.V128 lo hi) .V128 [lo, hi]
  | nullFunc : InitializerResolution store inst (.RefNull .FuncRef) .FuncRef [0#u64]
  | nullExtern : InitializerResolution store inst (.RefNull .ExternRef) .ExternRef [0#u64]
  | func (index : U32) (addr : runtime.FuncAddr) (reference : U64)
      (lookup : inst.funcs.val[index.val]? = some addr)
      (encoded : reference.val = addr.index.val + 1) :
      InitializerResolution store inst (.RefFunc index) .FuncRef [reference]
  | global (ty : Itasca.wasm_types.ValueType) (index : U32) (addr : runtime.GlobalAddr) (value : runtime.store.GlobalInst)
      (lookup : inst.globals.val[index.val]? = some addr)
      (resolved : store.globals.val[addr.index.val]? = some value)
      (typed : value.ty.valtype = ty) (scalar : ty ≠ .V128) :
      InitializerResolution store inst (.GlobalGet index) ty [value.lo]
  | global2 (index : U32) (addr : runtime.GlobalAddr) (value : runtime.store.GlobalInst)
      (lookup : inst.globals.val[index.val]? = some addr)
      (resolved : store.globals.val[addr.index.val]? = some value)
      (vector : value.ty.valtype = .V128) :
      InitializerResolution store inst (.GlobalGet index) .V128 [value.lo, value.hi]

theorem InitializerResolution.width {M : Type} {store : runtime.store.Store M}
    {inst expr ty words} (resolved : InitializerResolution store inst expr ty words) :
    (Compiler.initializerWidth ty).val = words.length := by
  cases resolved <;> simp_all [Compiler.initializerWidth]

theorem InitializerResolution.read {M : Type} {store : runtime.store.Store M}
    {inst expr ty words} (resolved : InitializerResolution store inst expr ty words)
    (code : runtime.bytecode.CompiledFunction) (instruction : runtime.bytecode.Instr)
    (compiled : Compiler.InitialInstruction code expr ty instruction) :
    InitialRead store inst code instruction words := by
  cases resolved <;> cases compiled
  all_goals try first
    | exact .const32 _
    | exact .const64 _
    | exact .null
    | exact .func _ _ _ (by assumption) (by assumption)
    | exact .global _ _ _ (by assumption) (by assumption)
    | exact .global2 _ _ _ (by assumption) (by assumption)
    | contradiction
  rename_i lo hi pool embedded
  simpa [initializer_bits_low, initializer_bits_high] using
    (InitialRead.vector (store := store) (inst := inst) pool (Compiler.initializerBits lo hi) embedded)

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

/-- Compiler syntax plus source-value resolution suffices for the actual
synthetic entry point; no interpreter-correctness premise is hidden in either. -/
theorem synthetic_resolved_initializer (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) (words : List U64)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hc : inst.module.functions.val[function.val]? = some code)
    (compiled : Compiler.InitializerCode code expr ty)
    (resolved : InitializerResolution store inst expr ty words) :
    runtime.interp.run_synthetic memory hooks floats allocator store platform instIndex function
      ⦃ out => out.2.1 = store ∧ out.2.2 = platform ∧
        ∀ pair, out.1 = .Ok pair → pair = ((words[0]?).getD 0#u64, (words[1]?).getD 0#u64) ⦄ := by
  obtain ⟨instruction, hop, hcode⟩ := compiled.code
  apply synthetic_initializer memory hooks floats allocator law store platform instIndex function
    inst code instruction words hi hc (resolved.read code instruction hop)
    (by rw [compiled.capacity]; exact resolved.width)
  simpa [compiled.capacity] using hcode

end Itasca.Runtime.Interp

end

/-! ## Range -/

section

/-! The extracted range guard checks subtraction before addition and casts only
bounded endpoints. This holds at both supported machine-index widths. -/
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem usize_to_u64_exact (value : Usize) :
    (UScalar.cast .U64 value).val = value.val := by
  apply UScalar.cast_val_mod_pow_of_inBounds_eq
  rcases Usize.bounds_eq with h | h <;> scalar_tac

def RangeEffect (start len : U64) (size : Usize) (trap : runtime.Trap)
    (result : core.result.Result (core.ops.range.Range Usize) runtime.ExecError) : Prop :=
  if start.val + len.val ≤ size.val then
    ∃ range, result = .Ok range ∧ range.start.val = start.val ∧ range.end.val = start.val + len.val
  else result = .Err (.Trap trap)

@[step] theorem range_effect (start len : U64) (size : Usize) (trap : runtime.Trap) :
    runtime.range start len size trap ⦃ result => RangeEffect start len size trap result ⦄ := by
  have sizeCast := usize_to_u64_exact size
  unfold runtime.range
  simp only [lift, bind_ok]
  split
  · rename_i outside
    simp only [WP.spec_ok, RangeEffect]
    split
    · scalar_tac
    · trivial
  · rename_i inside
    step as ⟨remaining, hremaining⟩
    split
    · rename_i outside
      simp only [WP.spec_ok, RangeEffect]
      split
      · scalar_tac
      · trivial
    · rename_i insideLength
      have fits : start.val + len.val ≤ size.val := by scalar_tac
      have startCast := cast_usize_exact start (by scalar_tac)
      step as ⟨last, hlast⟩
      have endCast := cast_usize_exact last (by scalar_tac)
      simp [RangeEffect, fits, startCast, endCast, hlast]

end Itasca.Runtime.Interp

end

/-! ## ControlEntry -/

section

namespace Itasca.Runtime.Interp
open Aeneas.Std

theorem block_signature_resolves (m : moduleinst) (bt : blocktype) (params results : List valtype)
    (signature : Compiler.BlockSignature m.TYPES bt params results) :
    SourceMachine.blockType m bt = some ⟨.mk_list params, .mk_list results⟩ := by
  cases signature with
  | empty => rfl
  | value ty => rfl
  | index i params results lookup => exact lookup

theorem block_source_step (s : store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (bt : blocktype) (body after : List instr) (front params results : List valtype)
    (signature : Compiler.BlockSignature f.module.TYPES bt params results)
    (shape : f.vals.map Compiler.valueType = front ++ params) :
    SourceMachine.astep ⟨s, ambient, { f with code := .BLOCK bt body :: after } :: rest, []⟩ =
      .next ⟨s, ambient, { f with code := body, labels := ⟨results, results, [], front.length, after⟩ :: f.labels } :: rest, []⟩ := by
  have size : f.vals.length = front.length + params.length := by
    simpa only [List.length_map, List.length_append] using congrArg List.length shape
  have height : f.vals.length - params.length = front.length := by omega
  have args : (f.vals.drop (f.vals.length - params.length)).map SourceMachine.valueType = params := by
    rw [show SourceMachine.valueType = Compiler.valueType from (funext value_type_eq_abs).symm,
      List.map_drop, height, shape, List.drop_left]
  rw [height] at args
  have resolved := block_signature_resolves f.module bt params results signature
  simp [SourceMachine.astep, SourceMachine.enterLabel, resolved, height, args, show params.length ≤ f.vals.length by omega, SourceMachine.advance]

theorem LabelsMatch.enter {values : List val} {labels : List SourceMachine.Label} {targets : List Compiler.LabelTarget}
    (outer : LabelsMatch values labels targets) (front params results branchTypes : List valtype)
    (branch : U32) (normalExit : Nat) (cont after : List instr) {normalLive branchLive : Bool}
    (shape : values.map Compiler.valueType = front ++ params) :
    LabelsMatch values (⟨branchTypes, results, cont, front.length, after⟩ :: labels)
      (⟨front, branchTypes, results, branch, normalExit, cont, after, normalLive, branchLive⟩ :: targets) := by
  refine ⟨by simp only [List.length_cons, outer.length], ?_⟩
  intro depth label lookup
  cases depth with
  | zero =>
    have same : label = ⟨branchTypes, results, cont, front.length, after⟩ := by simpa using lookup.symm
    subst label
    refine ⟨_, rfl, ⟨?_, rfl, rfl, rfl, rfl, rfl⟩⟩
    simp only [List.map_take, shape, List.take_left]
  | succ depth =>
    obtain ⟨target, found, matching⟩ := outer.atIndex depth label (by simpa using lookup)
    exact ⟨target, by simpa using found, matching⟩

theorem loop_source_step (s : store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (bt : blocktype) (body after : List instr) (front params results : List valtype)
    (signature : Compiler.BlockSignature f.module.TYPES bt params results)
    (shape : f.vals.map Compiler.valueType = front ++ params) :
    SourceMachine.astep ⟨s, ambient, { f with code := .LOOP bt body :: after } :: rest, []⟩ =
      .next ⟨s, ambient, { f with code := body, labels := ⟨params, results, [.LOOP bt body], front.length, after⟩ :: f.labels } :: rest, []⟩ := by
  have size : f.vals.length = front.length + params.length := by
    simpa only [List.length_map, List.length_append] using congrArg List.length shape
  have height : f.vals.length - params.length = front.length := by omega
  have args : (f.vals.drop (f.vals.length - params.length)).map SourceMachine.valueType = params := by
    rw [show SourceMachine.valueType = Compiler.valueType from (funext value_type_eq_abs).symm,
      List.map_drop, height, shape, List.drop_left]
  rw [height] at args
  have resolved := block_signature_resolves f.module bt params results signature
  simp [SourceMachine.astep, SourceMachine.enterLabel, resolved, height, args, show params.length ≤ f.vals.length by omega, SourceMachine.advance]

end Itasca.Runtime.Interp

end

/-! ## Erased -/

section

/-! Source reductions whose compiler emission is empty. They advance the
abstract continuation while retaining the actual bytecode position and slot
storage; dead dropped words remain outside the live value relation. -/
namespace Itasca.Runtime.Interp
open Aeneas.Std

theorem linear_emission_nop_inv {locals before after : List valtype} {emitted : List Compiler.Bytecode}
    (h : Compiler.LinearEmission locals before .NOP emitted after) : emitted = [] ∧ after = before := by
  generalize equality : instr.NOP = instruction at h
  cases h with
  | binary stack ity op left right hl hr => cases op <;> simp_all [Compiler.IntegerBinary.source]
  | numeric stack op a b ha hb =>
    have decoded := congrArg SourceMachine.Numeric.decodeInstruction equality
    rw [SourceMachine.Numeric.decode_instruction_source] at decoded
    simp [SourceMachine.Numeric.decode_instruction_source, SourceMachine.Numeric.decodeInstruction] at decoded
  | _ => simp_all

theorem linear_emission_drop_inv {locals before after : List valtype} {emitted : List Compiler.Bytecode}
    (h : Compiler.LinearEmission locals before .DROP emitted after) :
    ∃ stack ty, before = stack ++ [ty] ∧ after = stack ∧ emitted = [] := by
  generalize equality : instr.DROP = instruction at h
  cases h with
  | drop stack ty => exact ⟨_, ty, rfl, rfl, rfl⟩
  | binary stack ity op left right hl hr => cases op <;> simp_all [Compiler.IntegerBinary.source]
  | numeric stack op a b ha hb =>
    have decoded := congrArg SourceMachine.Numeric.decodeInstruction equality
    rw [SourceMachine.Numeric.decode_instruction_source] at decoded
    simp [SourceMachine.Numeric.decode_instruction_source, SourceMachine.Numeric.decodeInstruction] at decoded
  | _ => simp_all

end Itasca.Runtime.Interp

end

/-! ## SourceClosure -/

section

namespace Itasca.Runtime.Interp

/-- Every ordinary source rearrangement preserves an arbitrary pre-existing finite bound on source continuations. -/
structure SourceClosure (before after : SourceMachine.AFrame) : Prop where
  bounded : ∀ bound, SourceMachine.FrameCodeBound bound before → SourceMachine.FrameCodeBound bound after
  references : ∀ bound, SourceMachine.FrameReferencesBound bound before → SourceMachine.FrameReferencesBound bound after

theorem SourceClosure.refl (f : SourceMachine.AFrame) : SourceClosure f f := ⟨fun _ h => h, fun _ h => h⟩

theorem SourceClosure.trans {before middle after} (first : SourceClosure before middle)
    (second : SourceClosure middle after) : SourceClosure before after :=
  ⟨fun bound h => second.bounded bound (first.bounded bound h),
    fun bound h => second.references bound (first.references bound h)⟩

theorem SourceClosure.tail (f : SourceMachine.AFrame) (op : instr) (after : List instr)
    (locals values : List val)
    (references : ∀ bound, SourceMachine.FrameReferencesBound bound f → SourceMachine.ValuesBound bound locals ∧ SourceMachine.ValuesBound bound values) :
    SourceClosure { f with code := op :: after } { f with code := after, locals := locals, vals := values } := by
  refine ⟨?_, references⟩
  rintro bound ⟨size, labels⟩
  refine ⟨?_, labels⟩
  change sizeOf after ≤ bound
  simp only [List.cons.sizeOf_spec] at size
  omega

theorem SourceClosure.if_choice (f : SourceMachine.AFrame) (bt : blocktype) (yes no after : List instr)
    (condition : Bool) (values : List val)
    (references : ∀ bound, SourceMachine.ValuesBound bound f.vals → SourceMachine.ValuesBound bound values) :
    SourceClosure { f with code := .IFELSE bt yes no :: after }
      { f with code := .BLOCK bt (if condition then yes else no) :: after, vals := values } := by
  refine ⟨?_, fun bound h => ⟨h.1, references bound h.2⟩⟩
  rintro bound ⟨size, labels⟩
  refine ⟨?_, labels⟩
  cases condition <;> simp at size ⊢ <;> omega

theorem SourceClosure.loop (f : SourceMachine.AFrame) (bt : blocktype) (body after : List instr)
    (params results : List valtype) (height : Nat) :
    SourceClosure { f with code := .LOOP bt body :: after }
      { f with code := body, labels := ⟨params, results, [.LOOP bt body], height, after⟩ :: f.labels } := by
  refine ⟨?_, fun _ h => h⟩
  rintro bound ⟨size, labels⟩
  constructor
  · simp at size ⊢
    omega
  · intro label member
    rcases List.mem_cons.mp member with rfl | member
    · simpa using size
    · exact labels label member

theorem SourceClosure.block (f : SourceMachine.AFrame) (bt : blocktype) (body after : List instr)
    (results : List valtype) (height : Nat) :
    SourceClosure { f with code := .BLOCK bt body :: after }
      { f with code := body, labels := ⟨results, results, [], height, after⟩ :: f.labels } := by
  refine ⟨?_, fun _ h => h⟩
  rintro bound ⟨size, labels⟩
  constructor
  · simp at size ⊢
    omega
  · intro label member
    rcases List.mem_cons.mp member with rfl | member
    · simp at size ⊢
      omega
    · exact labels label member

theorem SourceClosure.label (f : SourceMachine.AFrame) (label : SourceMachine.Label) (labels : List SourceMachine.Label) :
    SourceClosure { f with code := [], labels := label :: labels }
      { f with code := label.after, labels := labels } := by
  refine ⟨?_, fun _ h => h⟩
  rintro bound ⟨size, saved⟩
  have full := saved label (List.mem_cons_self ..)
  have appended := SourceMachine.list_size_append label.cont label.after
  have positive : 1 ≤ sizeOf label.cont := by cases label.cont <;> simp <;> omega
  exact ⟨by change sizeOf label.after ≤ bound; omega, fun next member => saved next (List.mem_cons_of_mem _ member)⟩

theorem SourceClosure.code_bound {before after} (closure : SourceClosure before after)
    {s : store} {ambient : frame} {rest : List SourceMachine.AFrame} {bound : Nat}
    (bounded : SourceMachine.CodeBound bound ⟨s, ambient, before :: rest, []⟩) :
    SourceMachine.CodeBound bound ⟨s, ambient, after :: rest, []⟩ :=
  SourceMachine.bound_replace_frame bounded (closure.bounded bound (bounded.frames before (List.mem_cons_self ..)))

end Itasca.Runtime.Interp

end
