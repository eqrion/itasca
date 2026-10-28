import Itasca.Runtime.Interp.Relations.InitializerResolution
import Itasca.Runtime.Interp.Relations.DecodeValue
import Itasca.Runtime.Store.Preparation.Staging
import Itasca.Runtime.Store.Invariant.ValueRead

/-! The real instantiation constant-expression wrapper is read-only and total
under compiler syntax, resolved source operands, and the reference-index bound
needed by the public primitive decoder. These premises mention no execution
result or termination property. -/
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem eval_const_effect (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (expr : Itasca.types.ConstExpr) (ty : Itasca.types.ValueType) (words : List U64)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hc : inst.module.functions.val[function.val]? = some code)
    (compiled : Code.InitializerCode code expr ty)
    (resolved : Interp.InitializerResolution store inst expr ty words)
    (referenceBound : ty = .FuncRef ∨ ty = .ExternRef → ((words[0]?).getD 0#u64).val ≤ Usize.max) :
    runtime.interp.eval_const memory hooks floats allocator store platform instIndex function ty
      ⦃ out => out.2.1 = store ∧ out.2.2 = platform ∧
        ∀ value, out.1 = .Ok value → Interp.rawType value = ty ∧
          Interp.sourceValue value = decodeWords ty ((words[0]?).getD 0#u64) ((words[1]?).getD 0#u64) ⦄ := by
  unfold runtime.interp.eval_const
  step with Interp.synthetic_resolved_initializer memory hooks floats allocator law store platform
    instIndex function inst code expr ty words hi hc compiled resolved
    as ⟨result, store', platform', hs, hp, success⟩
  subst store' platform'
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    have hpair := success pair rfl
    subst pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with Interp.decode_value_boundary ty ((words[0]?).getD 0#u64) ((words[1]?).getD 0#u64)
      store.id referenceBound as ⟨value, hty, hvalue⟩
    simp_all

/-- Only the function-address map and already-created global contents are needed
while instantiation is staged; a complete store typing invariant is unnecessary. -/
structure InitializerBindings {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) : Prop where
  funcs : ∀ address ∈ inst.funcs.val, address.index.val < store.funcs.length
  globals : ∀ global ∈ store.globals.val, GlobalShape store global

def initializerGlobal (ty : Itasca.types.ValueType) (words : List U64) : runtime.store.GlobalInst :=
  { ty := { mutability := .Const, valtype := ty },
    lo := (words[0]?).getD 0#u64, hi := (words[1]?).getD 0#u64 }

theorem initializer_global_shape {store : runtime.store.Store M} {inst expr ty words}
    (resolved : Interp.InitializerResolution store inst expr ty words)
    (bindings : InitializerBindings store inst) : GlobalShape store (initializerGlobal ty words) := by
  cases resolved with
  | i32 value => simp [initializerGlobal, GlobalShape]; scalar_tac
  | i64 value => simp [initializerGlobal, GlobalShape]
  | f32 bits => simp [initializerGlobal, GlobalShape]; scalar_tac
  | f64 bits => simp [initializerGlobal, GlobalShape]
  | vector lo hi => simp [initializerGlobal, GlobalShape]
  | nullFunc => simp [initializerGlobal, GlobalShape, ReferenceShape]
  | nullExtern => simp [initializerGlobal, GlobalShape, ReferenceShape]
  | func index addr reference lookup encoded =>
    have bound := bindings.funcs addr (List.mem_of_getElem? lookup)
    change addr.index.val < store.funcs.val.length at bound
    simp [initializerGlobal, GlobalShape, ReferenceShape]
    right
    omega
  | global ty index addr value lookup found typed scalar =>
    have hg := bindings.globals value (List.mem_of_getElem? found)
    cases ty <;> simp_all [initializerGlobal, GlobalShape]
  | global2 index addr value lookup found vector =>
    simp [initializerGlobal, GlobalShape]

theorem initializer_reference_bound {store : runtime.store.Store M} {inst expr ty words}
    (resolved : Interp.InitializerResolution store inst expr ty words)
    (bindings : InitializerBindings store inst)
    (reference : ty = .FuncRef ∨ ty = .ExternRef) :
    ((words[0]?).getD 0#u64).val ≤ Usize.max := by
  have shape := initializer_global_shape resolved bindings
  rcases reference with rfl | rfl
  · exact (show ReferenceShape store .FuncRef ((words[0]?).getD 0#u64) from shape.1).word_bound _ _ _
  · exact (show ReferenceShape store .ExternRef ((words[0]?).getD 0#u64) from shape.1).word_bound _ _ _

/-- The instantiated initializer result is an issued, typed API value, so it can
safely pass through the generic global-definition boundary. -/
theorem eval_const_owned (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (expr : Itasca.types.ConstExpr) (ty : Itasca.types.ValueType) (words : List U64)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hc : inst.module.functions.val[function.val]? = some code)
    (compiled : Code.InitializerCode code expr ty)
    (resolved : Interp.InitializerResolution store inst expr ty words)
    (bindings : InitializerBindings store inst) :
    runtime.interp.eval_const memory hooks floats allocator store platform instIndex function ty
      ⦃ out => out.2.1 = store ∧ out.2.2 = platform ∧
        ∀ value, out.1 = .Ok value → ValueInStore store value ∧ Interp.rawType value = ty ⦄ := by
  unfold runtime.interp.eval_const
  step with Interp.synthetic_resolved_initializer memory hooks floats allocator law store platform
    instIndex function inst code expr ty words hi hc compiled resolved
    as ⟨result, store', platform', hs, hp, success⟩
  subst store' platform'
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    have hpair := success pair rfl
    subst pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    have owned := decode_global_owned store (initializerGlobal ty words) (initializer_global_shape resolved bindings)
    obtain ⟨value, decoded, hty, hvalue⟩ := WP.spec_imp_exists
      (Interp.decode_value_boundary ty ((words[0]?).getD 0#u64) ((words[1]?).getD 0#u64)
        store.id (initializer_reference_bound resolved bindings))
    change runtime.value.decode ty ((words[0]?).getD 0#u64) ((words[1]?).getD 0#u64) store.id
      ⦃ value => ValueInStore store value ⦄ at owned
    rw [decoded] at owned
    simp only [WP.spec_ok] at owned
    have combined : runtime.value.decode ty ((words[0]?).getD 0#u64) ((words[1]?).getD 0#u64) store.id
        ⦃ result => ValueInStore store result ∧ Interp.rawType result = ty ⦄ :=
      WP.exists_imp_spec ⟨value, decoded, owned, hty⟩
    step with combined as ⟨actual, howned, htyped⟩
    simp [howned, htyped]

end Itasca.Runtime.Store
