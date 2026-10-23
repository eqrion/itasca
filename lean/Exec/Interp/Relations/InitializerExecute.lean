import Exec.Interp.Relations.Fetch
import Exec.Interp.Relations.Copy

/-! Exact effects of the read-only instruction handlers used by retained
constant-initializer functions. Store lookups are explicit premises, independent
of any execution-correctness certificate. -/
namespace Exec.Interp
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

theorem copyWords_self (words : List U64) (src n : Nat) (h : src + n ≤ words.length) :
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
    simpa [copyWords_self exec.slots.val 0 width.val (by simpa using hwidth)] using hslots
  exact ⟨hok, he, hframes, by simpa [he] using hrest⟩

end Exec.Interp
