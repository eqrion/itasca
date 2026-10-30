import Itasca.Runtime.Store.Initialization.Initializer
import Itasca.Module.Const.Syntax

/-! Validator constant typing resolves to concrete initializer words using only
issued function maps and the linked imported-global prefix. -/
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The maps prepared by linking cover the source constant-expression context.
Only imported globals are required: validated initializers cannot read a newly
defined global, including one whose initialization has already completed. -/
structure InitializerImports {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) : Prop where
  funcs : inst.module.module.env.func_types.val.length ≤ inst.funcs.val.length
  globals : ∀ index : U32, ∀ ty : Itasca.wasm_types.GlobalType,
    inst.module.module.env.global_types.val[index.val]? = some ty →
    index.val < inst.module.module.env.num_imported_globals.val →
    ∃ addr value, inst.globals.val[index.val]? = some addr ∧
      store.globals.val[addr.index.val]? = some value ∧ value.ty = ty

/-- Source constant typing supplies the resolution relation used by the machine
proof. The encoded reference bound follows from the issued store address. -/
theorem initializer_resolves {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (expr : Itasca.wasm_types.ConstExpr)
    (ty : Itasca.wasm_types.ValueType)
    (valid : Itasca.ModuleConstants.Valid inst.module.module.env expr ty)
    (bindings : InitializerBindings store inst)
    (imports : InitializerImports store inst) :
    ∃ words, Interp.InitializerResolution store inst expr ty words := by
  cases valid with
  | i32 value => exact ⟨_, .i32 value⟩
  | i64 value => exact ⟨_, .i64 value⟩
  | f32 value => exact ⟨_, .f32 value⟩
  | f64 value => exact ⟨_, .f64 value⟩
  | v128 lo hi => exact ⟨_, .vector lo hi⟩
  | refNull ty =>
    cases ty with
    | FuncRef => exact ⟨_, .nullFunc⟩
    | ExternRef => exact ⟨_, .nullExtern⟩
  | refFunc index hi =>
    have bound : index.val < inst.funcs.val.length := by have := imports.funcs; omega
    let addr := inst.funcs.val[index.val]
    have lookup : inst.funcs.val[index.val]? = some addr := List.getElem?_eq_getElem bound
    have issued := bindings.funcs addr (List.mem_of_getElem? lookup)
    have encodedBound : addr.index.val + 1 < 2 ^ UScalarTy.U64.numBits := by
      have capacity := store.funcs.property
      rcases Usize.bounds_eq with h | h <;> scalar_tac
    let reference : U64 := UScalar.ofNatCore (addr.index.val + 1) encodedBound
    exact ⟨_, .func index addr reference lookup (UScalar.ofNatCore_val_eq encodedBound)⟩
  | globalGet index gt hi hgt imported immutable =>
    have lookup : inst.module.module.env.global_types.val[index.val]? = some gt := by
      rw [List.getElem?_eq_getElem hi, hgt]
    obtain ⟨addr, value, ha, hv, hty⟩ := imports.globals index gt lookup imported
    by_cases vector : gt.valtype = .V128
    · rw [vector]
      exact ⟨_, .global2 index addr value ha hv (by simpa [hty] using vector)⟩
    · exact ⟨_, .global gt.valtype index addr value ha hv (by rw [hty]) vector⟩

/-- Linking facts remain valid while defined globals and their addresses append. -/
theorem InitializerImports.extend {M : Type}
    {before after : runtime.store.Store M} {old next : runtime.store.ModuleInst}
    (imports : InitializerImports before old)
    (source : next.module = old.module) (functions : next.funcs = old.funcs)
    (globalMap : next.globals.val.take old.globals.length = old.globals.val)
    (globals : after.globals.val.take before.globals.length = before.globals.val) :
    InitializerImports after next := by
  constructor
  · simpa [source, functions] using imports.funcs
  · intro index ty typed imported
    rw [source] at typed imported
    obtain ⟨addr, value, found, read, htype⟩ := imports.globals index ty typed imported
    refine ⟨addr, value, ?_, ?_, htype⟩
    · have bound := (List.getElem?_eq_some_iff.mp found).1
      rw [← globalMap, List.getElem?_take] at found
      simpa [bound] using found
    · have bound := (List.getElem?_eq_some_iff.mp read).1
      rw [← globals, List.getElem?_take] at read
      simpa [bound] using read

end Itasca.Runtime.Store
