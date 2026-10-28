import Exec.Interp.Relations.Synthetic

/-! Resolve retained initializer certificates against concrete instance maps.
The resolution relation describes source literals and store reads only; the
machine theorem is derived from it and the compiler's syntactic certificate. -/
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem initializerBits_low (lo hi : U64) :
    UScalar.cast .U64 (Code.initializerBits lo hi) = lo := by
  apply U64.bv_eq_imp_eq
  simp only [Code.initializerBits, UScalar.cast_bv_eq]
  apply BitVec.eq_of_getLsbD_eq
  intro i h
  change i < 64 at h
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  simp [h, show i < 128 by omega, show ¬64 ≤ i by omega]

theorem initializerBits_high (lo hi : U64) :
    UScalar.cast .U64 (⟨(Code.initializerBits lo hi).bv >>> 64⟩ : U128) = hi := by
  apply U64.bv_eq_imp_eq
  simp only [Code.initializerBits, UScalar.cast_bv_eq]
  apply BitVec.eq_of_getLsbD_eq
  intro i h
  change i < 64 at h
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  simp [h, show 64 + i < 128 by omega, show i < 128 by omega]

inductive InitializerResolution {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) :
    Itasca.types.ConstExpr → Itasca.types.ValueType → List U64 → Prop where
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
  | global (ty : Itasca.types.ValueType) (index : U32) (addr : runtime.GlobalAddr) (value : runtime.store.GlobalInst)
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
    (Code.initializerWidth ty).val = words.length := by
  cases resolved <;> simp_all [Code.initializerWidth]

theorem InitializerResolution.read {M : Type} {store : runtime.store.Store M}
    {inst expr ty words} (resolved : InitializerResolution store inst expr ty words)
    (code : runtime.bytecode.CompiledFunction) (instruction : runtime.bytecode.Instr)
    (compiled : Code.InitialInstruction code expr ty instruction) :
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
  simpa [initializerBits_low, initializerBits_high] using
    (InitialRead.vector (store := store) (inst := inst) pool (Code.initializerBits lo hi) embedded)

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

/-- Compiler syntax plus source-value resolution suffices for the actual
synthetic entry point; no interpreter-correctness premise is hidden in either. -/
theorem synthetic_resolved_initializer (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (expr : Itasca.types.ConstExpr) (ty : Itasca.types.ValueType) (words : List U64)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hc : inst.module.functions.val[function.val]? = some code)
    (compiled : Code.InitializerCode code expr ty)
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
