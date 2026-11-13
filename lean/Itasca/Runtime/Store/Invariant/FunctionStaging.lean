import Itasca.Runtime.Store.Preparation.Staging
import Itasca.Runtime.Store.Invariant.Typing
import Itasca.Runtime.Spec.Integer
import Itasca.Runtime.Interp.Relations.Defaults
import Itasca.Runtime.Store.Api.DefineTable
import Itasca.Runtime.Representation.StoreCapacity

/-!
Sections, each formerly its own module: Extension, ValueDecode, ValueRead, InvalidWrite, TypeStaging, FunctionStaging.
-/

/-! ## Extension -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

private theorem prefix_lookup {T : Type} (before after : List T)
    (hprefix : after.take before.length = before) (index : Nat) (hi : index < before.length) :
    after[index]? = before[index]? := by
  have h := congrArg (fun xs => xs[index]?) hprefix
  simpa [List.getElem?_take, hi] using h

private theorem prefix_get_d_map {T U : Type} (before after : List T) (f : T → U) (fallback : U)
    (hprefix : after.take before.length = before) (index : Nat) (hi : index < before.length) :
    (after.map f).getD index fallback = (before.map f).getD index fallback := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
    prefix_lookup before after hprefix index hi]

/-- Canonical signature insertion does not change the types in an existing
instance's decoded module environment. -/
theorem decode_instance_prefix {M : Type} (before after : runtime.store.Store M)
    (hprefix : StagedPrefix before after) (inst : runtime.store.ModuleInst)
    (hinst : InstanceShape before inst) : decodeInstance after inst = decodeInstance before inst := by
  unfold decodeInstance
  congr 1
  apply List.map_congr_left
  intro index hindex
  exact prefix_get_d_map _ _ decodeFuncType default hprefix.types index.val (hinst.2.2.2.2.2.2.2.1 index hindex)

/-- Existing function instances retain both their signature and defining module
when new objects and canonical signatures are appended during instantiation. -/
theorem decode_function_prefix {M : Type} (code : CodeInterpretation)
    (before after : runtime.store.Store M) (hprefix : StagedPrefix before after)
    (view : M → Slice U8) (shape : Shape view before)
    (function : runtime.store.FuncInst) (hfunction : function ∈ before.funcs.val) :
    decodeFunction code after function = decodeFunction code before function := by
  have hf := shape.functions function hfunction
  unfold decodeFunction
  rw [prefix_get_d_map _ _ decodeFuncType default hprefix.types function.signature.val hf.1]
  cases hc : function.code with
  | Host id => rfl
  | Wasm index fn =>
    have h := hf.2
    simp only [hc] at h
    obtain ⟨inst, hlookup, hfn⟩ := h
    have hib : index.val < before.instances.length := by
      exact List.getElem?_eq_some_iff.mp hlookup |>.1
    have hnew := prefix_lookup before.instances.val after.instances.val hprefix.instances index.val hib
    simp only [hnew, hlookup]
    rw [decode_instance_prefix before after hprefix inst (shape.instances inst (List.mem_of_getElem? hlookup))]

/-- Appending raw store objects preserves every decoded object already present.
The proof includes the indirect dependency of function instances on the
canonical signature pool and defining instance maps. -/
theorem decode_store_prefix {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (before after : runtime.store.Store M) (shape : Shape view before)
    (hprefix : StagedPrefix before after) :
    let old := decodeStore view code before
    let fresh := decodeStore view code after
    fresh.FUNCS.take old.FUNCS.length = old.FUNCS ∧
    fresh.GLOBALS.take old.GLOBALS.length = old.GLOBALS ∧
    fresh.TABLES.take old.TABLES.length = old.TABLES ∧
    fresh.MEMS.take old.MEMS.length = old.MEMS ∧
    fresh.ELEMS.take old.ELEMS.length = old.ELEMS ∧
    fresh.DATAS.take old.DATAS.length = old.DATAS := by
  simp only [decodeStore, List.length_map, ← List.map_take]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hprefix.funcs]
    apply List.map_congr_left
    intro function hfunction
    exact decode_function_prefix code before after hprefix view shape function hfunction
  · rw [hprefix.globals]
  · rw [hprefix.tables]
  · rw [hprefix.memories]
  · rw [hprefix.elems]
  · rw [hprefix.datas]

private theorem prefix_length {T : Type} (before after : List T)
    (hprefix : after.take before.length = before) : before.length ≤ after.length := by
  have h := congrArg List.length hprefix
  simp only [List.length_take] at h
  exact h ▸ Nat.min_le_right _ _

private theorem prefix_get_bang {T : Type} [Inhabited T] (before after : List T)
    (hprefix : after.take before.length = before) (index : Nat) (hi : index < before.length) :
    after[index]! = before[index]! := by
  simp only [List.getElem!_eq_getElem?_getD, prefix_lookup before after hprefix index hi]

private theorem prefix_bounds {T : Type} (before after : List T)
    (hprefix : after.take before.length = before) :
    Forall (fun i => i < after.length) (List.range before.length) := by
  intro i hi
  exact Nat.lt_of_lt_of_le (List.mem_range.mp hi) (prefix_length before after hprefix)

private theorem prefix_rel {T : Type} [Inhabited T] (rel : T → T → Prop) (valid : T → Prop)
    (hrefl : ∀ value, valid value → rel value value) (before after : List T)
    (hprefix : after.take before.length = before) (hvalid : Forall valid before) :
    Forall (fun i => rel before[i]! after[i]!) (List.range before.length) := by
  intro i hi
  have hib := List.mem_range.mp hi
  rw [prefix_get_bang before after hprefix i hib]
  apply hrefl
  simpa only [getElem!_pos before i hib] using hvalid before[i] (List.getElem_mem hib)

/-- Exact retained prefixes are a sufficient concrete case of the specification's
store-extension relation, including its explicit well-formedness obligations. -/
theorem store_prefix_extends (before after : _root_.store)
    (hb : wf_store before) (ha : wf_store after)
    (hf : after.FUNCS.take before.FUNCS.length = before.FUNCS)
    (hg : after.GLOBALS.take before.GLOBALS.length = before.GLOBALS)
    (ht : after.TABLES.take before.TABLES.length = before.TABLES)
    (hm : after.MEMS.take before.MEMS.length = before.MEMS)
    (he : after.ELEMS.take before.ELEMS.length = before.ELEMS)
    (hd : after.DATAS.take before.DATAS.length = before.DATAS) :
    Extend_store before after := by
  have hwf : Forall wf_funcinst before.FUNCS := by cases hb; assumption
  have hwg : Forall wf_globalinst before.GLOBALS := by cases hb; assumption
  have hwt : Forall wf_tableinst before.TABLES := by cases hb; assumption
  have hwm : Forall wf_meminst before.MEMS := by cases hb; assumption
  have hwd : Forall wf_datainst before.DATAS := by cases hb; assumption
  apply Extend_store.mk_Extend_store

  · intro i hi; exact List.mem_range.mp hi
  · exact prefix_bounds before.GLOBALS after.GLOBALS hg
  · exact prefix_rel Extend_globalinst wf_globalinst Spec.extend_global_refl _ _ hg hwg
  · intro i hi; exact List.mem_range.mp hi
  · exact prefix_bounds before.MEMS after.MEMS hm
  · exact prefix_rel Extend_meminst wf_meminst Spec.extend_mem_refl _ _ hm hwm
  · intro i hi; exact List.mem_range.mp hi
  · exact prefix_bounds before.TABLES after.TABLES ht
  · exact prefix_rel Extend_tableinst wf_tableinst Spec.extend_table_refl _ _ ht hwt
  · intro i hi; exact List.mem_range.mp hi
  · exact prefix_bounds before.FUNCS after.FUNCS hf
  · exact prefix_rel Extend_funcinst wf_funcinst Spec.extend_func_refl _ _ hf hwf
  · intro i hi; exact List.mem_range.mp hi
  · exact prefix_bounds before.DATAS after.DATAS hd
  · exact prefix_rel Extend_datainst wf_datainst Spec.extend_data_refl _ _ hd hwd
  · intro i hi; exact List.mem_range.mp hi
  · exact prefix_bounds before.ELEMS after.ELEMS he
  · exact prefix_rel Extend_eleminst (fun _ => True) (fun value _ => Spec.extend_elem_refl value) _ _ he (by simp [Forall])
  · exact hb
  · exact ha

end Itasca.Runtime.Store

end

/-! ## ValueDecode -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem decode_words_code (ty : Itasca.wasm_types.ValueType) (lo hi : U64)
    (hfloat : ty = .F32 → lo.val < 2^32) :
    Compiler.decodeOne (Interp.sourceType ty) (Interp.pairWords ty (lo, hi)) =
      some (decodeWords ty lo hi, []) := by
  exact Interp.decode_words_code ty lo hi hfloat

/-- The concrete store decoder recovers the exact specification value from
words emitted by the actual extracted encoder, including all NaN payloads. -/
theorem decode_encoded_value {M : Type} (s : runtime.store.Store M)
    (value : runtime.Value) (hv : ValueInStore s value) (words : U64 × U64)
    (hencode : runtime.value.encode value = .ok words) :
    decodeWords (Interp.rawType value) words.1 words.2 = Interp.sourceValue value := by
  have hwords := Interp.encode_value_spec value s.id hv.1
  rw [hencode] at hwords
  simp only [WP.spec_ok] at hwords
  have hcanonical := encode_global_shape s value
    {mutability := .Const, valtype := Interp.rawType value} rfl hv
  rw [hencode] at hcanonical
  simp only [WP.spec_ok] at hcanonical
  have hfloat : Interp.rawType value = .F32 → words.1.val < 2^32 := by
    intro ht
    simp only [GlobalShape, ht] at hcanonical
    exact hcanonical.1
  have hround := Compiler.decode_encode (Interp.sourceValue value) (Interp.source_value_wf value) []
  simp only [List.append_nil, Interp.source_value_type] at hround
  rw [← hwords, decode_words_code _ _ _ hfloat] at hround
  exact congrArg Prod.fst (Option.some.inj hround)

end Itasca.Runtime.Store

end

/-! ## ValueRead -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Raw reference words fit the machine index type because they refer to a
retained object; zero remains the separate null sentinel. -/
theorem ReferenceShape.word_bound {M : Type} (s : runtime.store.Store M)
    (ty : Itasca.wasm_types.ElemType) (word : U64) (h : ReferenceShape s ty word) :
    word.val ≤ Usize.max := by
  rcases h with hzero | hindex
  · scalar_tac
  · cases ty <;> dsimp at hindex <;> scalar_tac

/-- Decoding canonical store words restores an owned API reference with an
existing address. This establishes the caller invariant for values obtained
through global and table accessors. -/
theorem decode_global_owned {M : Type} (s : runtime.store.Store M)
    (global : runtime.store.GlobalInst) (hg : GlobalShape s global) :
    runtime.value.decode global.ty.valtype global.lo global.hi s.id ⦃ value => ValueInStore s value ⦄ := by
  cases ht : global.ty.valtype <;> simp only [runtime.value.decode, ht]
  all_goals simp [lift, ValueInStore, Interp.ValueOwnedFits]
  case V128 => step
  case FuncRef =>
    simp only [GlobalShape, ht] at hg
    split
    · simp
    · rename_i hn
      have hbound := hg.1.word_bound s .FuncRef global.lo
      have hcast := cast_usize_exact global.lo hbound
      have hindex : global.lo.val - 1 < s.funcs.length := by
        rcases hg.1 with hz | hi
        · scalar_tac
        · exact hi
      step as ⟨index, hindexValue⟩
      scalar_tac
  case ExternRef =>
    simp only [GlobalShape, ht] at hg
    split
    · simp
    · rename_i hn
      have hbound := hg.1.word_bound s .ExternRef global.lo
      have hcast := cast_usize_exact global.lo hbound
      have hindex : global.lo.val - 1 < s.externs.length := by
        rcases hg.1 with hz | hi
        · scalar_tac
        · exact hi
      step as ⟨index, hindexValue⟩
      scalar_tac

end Itasca.Runtime.Store

end

/-! ## InvalidWrite -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

@[simp] theorem vec_set_current {T : Type} (values : alloc.vec.Vec T) (index : Usize)
    (hindex : index.val < values.length) : values.set index values.val[index.val] = values := by
  apply alloc.vec.Vec.ext
  simp [alloc.vec.Vec.set_val_eq, List.set_getElem_self]

end Itasca.Runtime.Store

end

/-! ## TypeStaging -/

section

/-!
Type interning and staging preserve context and type entries through the allocation loop. Resource classification remains a separate consumer shared with function staging.
-/

/-! ## Type Staging -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- A successful type-map entry names the exact canonical type; rejection
leaves both the store and provisional instance unchanged. -/
def TypeStageEffect {M : Type} (store : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (ty : Itasca.wasm_types.FuncType)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M × runtime.store.ModuleInst) : Prop :=
  (∃ error, out = (.Err error, store, inst)) ∨
  (∃ index addresses,
    InternEffect store ty (.Ok index, out.2.1) ∧
    addresses.val = inst.types.val ++ [index] ∧
    out.1 = .Ok () ∧ out.2.2 = {inst with types := addresses})

theorem add_instance_type_effect {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : Usize)
    (bound : index.val < inst.module.module.env.types.val.length)
    (objectBound : objectCount store ≤ Usize.max) (room : inst.types.length < Usize.max) :
    runtime.store.instantiate.Store.add_instance_type memory allocator store inst index
      ⦃ out => TypeStageEffect store inst inst.module.module.env.types.val[index.val] out ⦄ := by
  unfold runtime.store.instantiate.Store.add_instance_type
  simp only [runtime.compiler.ExecutableModule.env, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.types, bind_ok]
  have sliceBound : index.val < inst.module.module.env.types.deref.length := by
    simpa [alloc.vec.Vec.deref] using bound
  step as ⟨ty, read⟩
  have same : ty = inst.module.module.env.types.val[index.val] := by simpa [alloc.vec.Vec.deref] using read
  clear read
  subst ty
  step with intern_type_effect memory allocator law store _ objectBound as ⟨status, after, effect⟩
  rcases effect with ⟨error, failed⟩ | ⟨canonical, found, existing⟩ | ⟨types, count, appended, fresh, capacity, counter, limit, created⟩
  · cases failed
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, TypeStageEffect]
  · cases existing
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step as ⟨addresses, mapped⟩
    exact Or.inr ⟨canonical, addresses, Or.inr (Or.inl ⟨canonical, found, rfl⟩), mapped, rfl, rfl⟩
  · cases created
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step as ⟨addresses, mapped⟩
    exact Or.inr ⟨_, addresses, Or.inr (Or.inr ⟨types, count, appended, fresh, capacity, counter, limit, rfl⟩), mapped, rfl, rfl⟩

theorem InternEffect.lookup {M : Type} {store after : runtime.store.Store M}
    {ty : Itasca.wasm_types.FuncType} {index : Usize}
    (effect : InternEffect store ty (.Ok index, after)) : after.types.val[index.val]? = some ty := by
  rcases effect with ⟨error, failed⟩ | ⟨canonical, found, existing⟩ | ⟨types, count, appended, fresh, capacity, counter, limit, created⟩
  · cases failed
  · cases existing; exact found
  · cases created; simp [appended]

theorem InternEffect.staged {M : Type} {store after : runtime.store.Store M}
    {ty : Itasca.wasm_types.FuncType} {status}
    (effect : InternEffect store ty (status, after)) : StagedPrefix store after := by
  rcases effect with ⟨error, failed⟩ | ⟨canonical, found, existing⟩ | ⟨types, count, appended, fresh, capacity, counter, limit, created⟩
  · cases failed; exact .refl _
  · cases existing; exact .refl _
  · cases created; constructor <;> simp [appended]

theorem InternEffect.object_bound {M : Type} {store after : runtime.store.Store M}
    {ty : Itasca.wasm_types.FuncType} {status}
    (effect : InternEffect store ty (status, after)) (bound : objectCount store ≤ Usize.max) :
    objectCount after ≤ Usize.max := by
  rcases effect with ⟨error, failed⟩ | ⟨canonical, found, existing⟩ | ⟨types, count, appended, fresh, capacity, counter, limit, created⟩
  · cases failed; exact bound
  · cases existing; exact bound
  · cases created
    have maximum : store.limits.max_objects.val ≤ Usize.max := by scalar_tac
    have length := congrArg List.length appended
    simp only [List.length_append, List.length_singleton] at length
    unfold objectCount at *
    change types.val.length = store.types.length + 1 at length
    dsimp only
    change types.length = store.types.length + 1 at length
    omega

theorem InternEffect.only_types {M : Type} {store after : runtime.store.Store M}
    {ty : Itasca.wasm_types.FuncType} {status} (effect : InternEffect store ty (status, after)) :
    after = {store with types := after.types, signature_values := after.signature_values} := by
  rcases effect with ⟨error, failed⟩ | ⟨canonical, found, existing⟩ |
    ⟨types, count, appended, fresh, capacity, counter, limit, created⟩
  · cases failed; rfl
  · cases existing; rfl
  · cases created; rfl

theorem TypeEntries.extend {M : Type} {store after : runtime.store.Store M}
    {source : List Itasca.wasm_types.FuncType} {indices : List Usize}
    (entries : TypeEntries store source indices) (retained : StagedPrefix store after) :
    TypeEntries after source indices := by
  apply List.Forall₂.imp ?_ entries
  intro ty index found
  have bound := (List.getElem?_eq_some_iff.mp found).1
  rw [← retained.types, List.getElem?_take] at found
  simpa [bound] using found

theorem TypeStageEffect.context {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {ty : Itasca.wasm_types.FuncType} {out}
    (effect : TypeStageEffect store inst ty out) (bound : objectCount store ≤ Usize.max) :
    out.2.1 = {store with types := out.2.1.types, signature_values := out.2.1.signature_values} ∧
    out.2.2 = {inst with types := out.2.2.types} ∧ StagedPrefix store out.2.1 ∧
    objectCount out.2.1 ≤ Usize.max := by
  rcases effect with ⟨error, rfl⟩ | ⟨index, addresses, interned, mapped, ok, next⟩
  · exact ⟨rfl, rfl, .refl _, bound⟩
  · exact ⟨interned.only_types, by rw [next], interned.staged, interned.object_bound bound⟩

theorem TypeStageEffect.entries {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {ty : Itasca.wasm_types.FuncType} {out}
    (effect : TypeStageEffect store inst ty out) (success : out.1 = .Ok ())
    {source : List Itasca.wasm_types.FuncType} (entries : TypeEntries store source inst.types.val) :
    TypeEntries out.2.1 (source ++ [ty]) out.2.2.types.val := by
  rcases effect with ⟨error, failed⟩ | ⟨index, addresses, interned, mapped, ok, next⟩
  · rw [failed] at success; cases success
  · rw [next]
    dsimp only
    rw [mapped]
    exact List.rel_append (entries.extend interned.staged) (.cons interned.lookup .nil)

end Itasca.Runtime.Store

end

/-! ## Type Staging Loop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

def typeParts {M : Type} (store : runtime.store.Store M)
    (status : core.result.Result Unit runtime.ExecError) (inst : runtime.store.ModuleInst) :=
  (store, status, inst.module, inst.types, inst.funcs, inst.tables, inst.memories, inst.globals, inst.elems, inst.datas)

/-- Type canonicalization is total and preserves all other prepared maps. Its
successful type vector resolves every source signature to an exact store entry. -/
theorem type_staging_loop {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (seed inst : runtime.store.ModuleInst)
    (start : Usize) (startBound : start.val ≤ seed.module.module.env.types.val.length)
    (changed : store = {before with types := store.types, signature_values := store.signature_values})
    (instChanged : inst = {seed with types := inst.types})
    (retained : StagedPrefix before store) (objectBound : objectCount store ≤ Usize.max)
    (entries : TypeEntries store (seed.module.module.env.types.val.take start.val) inst.types.val) :
    runtime.store.instantiate.Store.prepare_instance_loop3 memory allocator store (.Ok ()) start inst
      ⦃ out => ∃ after next status, out = typeParts after status next ∧
        after = {before with types := after.types, signature_values := after.signature_values} ∧
        next = {seed with types := next.types} ∧ StagedPrefix before after ∧
        objectCount after ≤ Usize.max ∧
        (status = .Ok () → TypeEntries after seed.module.module.env.types.val next.types.val) ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop3
  apply loop.spec_decr_nat (fun state => seed.module.module.env.types.val.length - state.2.2.1.val)
    (fun state => state.1 = {before with types := state.1.types, signature_values := state.1.signature_values} ∧
      state.2.2.2 = {seed with types := state.2.2.2.types} ∧ StagedPrefix before state.1 ∧
      objectCount state.1 ≤ Usize.max ∧ state.2.2.1.val ≤ seed.module.module.env.types.val.length ∧
      (state.2.1 = .Ok () → TypeEntries state.1 (seed.module.module.env.types.val.take state.2.2.1.val)
        state.2.2.2.types.val))
  · rintro ⟨current, status, index, currentInst⟩ ⟨currentChanged, mapChanged, prefixStore, bound, indexBound, typing⟩
    dsimp only at currentChanged mapChanged prefixStore bound indexBound typing ⊢
    have source : currentInst.module = seed.module := by
      have eq := congrArg runtime.store.ModuleInst.module mapChanged
      exact eq
    unfold runtime.store.instantiate.Store.prepare_instance_loop3.body
    simp only [runtime.compiler.ExecutableModule.env, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.types, source, bind_ok]
    split
    · rename_i more
      have within : index.val < seed.module.module.env.types.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, currentInst, .Err error, by simp [typeParts, source], currentChanged, mapChanged, prefixStore, bound, by simp⟩
      | Ok value =>
        cases value
        have typed := typing rfl
        have mapSize : currentInst.types.val.length = index.val := by
          have lengths := typed.length_eq
          simpa [List.length_take, Nat.min_eq_left indexBound] using lengths.symm
        have maximum := seed.module.module.env.types.property
        have room : currentInst.types.length < Usize.max := by change currentInst.types.val.length < Usize.max; omega
        have actualBound : index.val < currentInst.module.module.env.types.val.length := by simpa only [source] using within
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step with add_instance_type_effect memory allocator law current currentInst index actualBound bound room
          as ⟨status, after, nextInst, effect⟩
        obtain ⟨afterChanged, nextChanged, prefixNext, nextBound⟩ := effect.context bound
        have afterExact : after = {before with types := after.types, signature_values := after.signature_values} := by
          calc
            after = {current with types := after.types, signature_values := after.signature_values} := afterChanged
            _ = _ := by rw [currentChanged]
        have nextExact : nextInst = {seed with types := nextInst.types} := by
          calc
            nextInst = {currentInst with types := nextInst.types} := nextChanged
            _ = _ := by rw [mapChanged]
        step as ⟨next, increment⟩
        refine ⟨afterExact, nextExact, prefixStore.trans prefixNext, nextBound, ?_, ?_, ?_⟩
        · omega
        · intro success
          have extended := effect.entries success typed
          rw [increment, List.take_succ_eq_append_getElem within]
          simpa only [source] using extended
        · omega
    · rename_i stopped
      have atEnd : index.val = seed.module.module.env.types.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      refine ⟨current, currentInst, status, by simp [typeParts, source], currentChanged, mapChanged, prefixStore, bound, ?_⟩
      intro success
      simpa only [atEnd, List.take_length] using typing success
  · exact ⟨changed, instChanged, retained, objectBound, startBound, fun _ => entries⟩

end Itasca.Runtime.Store

end

end

/-! ## FunctionStaging -/

section

/-!
Function staging effect, issued-address retention and allocation-loop preservation. Resource causes remain separate because they also depend on type allocation.
-/

/-! ## Function Staging -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The exact defined-function append, including its future instance identity
and canonical type index. No execution property of its body is assumed. -/
def FunctionStageEffect {M : Type} (store : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (instanceIndex index signature : Usize)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M × runtime.store.ModuleInst) : Prop :=
  (∃ error, out = (.Err error, store, inst)) ∨
  (∃ functions addresses,
    functions.val = store.funcs.val ++ [{signature, code := .Wasm instanceIndex index}] ∧
    addresses.val = inst.funcs.val ++ [{store := store.id, index := store.funcs.len}] ∧
    objectCount store < store.limits.max_objects.val ∧
    out = (.Ok (), {store with funcs := functions}, {inst with funcs := addresses}))

theorem add_instance_function_effect {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (instanceIndex index : Usize)
    (objectBound : objectCount store ≤ Usize.max)
    (bound : index.val < inst.module.module.env.func_type_indices.val.length)
    (typeBound : inst.module.module.env.func_type_indices.val[index.val].val < inst.types.val.length)
    (room : inst.funcs.length < Usize.max) :
    runtime.store.instantiate.Store.add_instance_function memory allocator store inst instanceIndex index
      ⦃ out => FunctionStageEffect store inst instanceIndex index
        inst.types.val[inst.module.module.env.func_type_indices.val[index.val].val] out ⦄ := by
  unfold runtime.store.instantiate.Store.add_instance_function
  step with room_spec memory store objectBound as ⟨available, capacity⟩
  rw [capacity]
  split
  · rename_i space
    simp [core.result.Result.Insts.CoreOpsTry.branch]
    obtain ⟨answer, reserved⟩ := reserve_wrapper_eq allocator law store.funcs 1#usize
    rw [reserved]
    cases answer
    · simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, FunctionStageEffect]
    · simp [core.result.Result.Insts.CoreOpsTry.branch,
        runtime.compiler.ExecutableModule.env,
        Itasca.metadata.Module.impl.env,
        Itasca.metadata.Env.impl.func_type_indices]
      have sourceBound : index.val < inst.module.module.env.func_type_indices.deref.length := by
        simpa [alloc.vec.Vec.deref] using bound
      step as ⟨sourceType, sourceRead⟩
      step as ⟨typeIndex, typeCast⟩
      have validType : typeIndex.val < inst.types.length := by
        simpa [typeCast, sourceRead, alloc.vec.Vec.deref] using typeBound
      step as ⟨signature, typeRead⟩
      have storeRoom : store.funcs.length < Usize.max := by
        unfold objectCount at space
        scalar_tac
      step as ⟨functions, appended⟩
      step as ⟨addresses, mapped⟩
      right
      refine ⟨functions, addresses, ?_, mapped, space, rfl⟩
      simpa [typeRead, typeCast, sourceRead, alloc.vec.Vec.deref] using appended
  · simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, FunctionStageEffect]

theorem FunctionStageEffect.context {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {instanceIndex index signature out}
    (effect : FunctionStageEffect store inst instanceIndex index signature out)
    (bound : objectCount store ≤ Usize.max) :
    out.2.1 = {store with funcs := out.2.1.funcs} ∧
    out.2.2 = {inst with funcs := out.2.2.funcs} ∧ StagedPrefix store out.2.1 ∧
    objectCount out.2.1 ≤ Usize.max ∧ out.2.2.funcs.length ≤ inst.funcs.length + 1 := by
  rcases effect with ⟨error, rfl⟩ | ⟨functions, addresses, appended, mapped, capacity, rfl⟩
  · exact ⟨rfl, rfl, .refl _, bound, by simp⟩
  · refine ⟨rfl, rfl, ?_, ?_, ?_⟩
    · constructor <;> simp [appended]
    · have maximum : store.limits.max_objects.val ≤ Usize.max := by scalar_tac
      have count : functions.length = store.funcs.length + 1 := by simpa using congrArg List.length appended
      unfold objectCount at *
      dsimp only
      omega
    · exact le_of_eq (by simpa using congrArg List.length mapped)

theorem FunctionStageEffect.issued {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {instanceIndex index signature out}
    (effect : FunctionStageEffect store inst instanceIndex index signature out)
    (issued : ∀ address ∈ inst.funcs.val, address.index.val < store.funcs.length) :
    ∀ address ∈ out.2.2.funcs.val, address.index.val < out.2.1.funcs.length := by
  rcases effect with ⟨error, rfl⟩ | ⟨functions, addresses, appended, mapped, capacity, rfl⟩
  · exact issued
  · have count : functions.length = store.funcs.length + 1 := by simpa using congrArg List.length appended
    intro address member
    simp only [mapped, List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · have bound := issued address old
      dsimp only
      omega
    · dsimp only
      simpa [count]

theorem FunctionStageEffect.count {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {instanceIndex index signature out}
    (effect : FunctionStageEffect store inst instanceIndex index signature out) (success : out.1 = .Ok ()) :
    out.2.2.funcs.length = inst.funcs.length + 1 := by
  rcases effect with ⟨error, failed⟩ | ⟨functions, addresses, appended, mapped, capacity, output⟩
  · rw [failed] at success; cases success
  · rw [output]
    simpa using congrArg List.length mapped

end Itasca.Runtime.Store

end

/-! ## Function Staging Loop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The actual defined-function allocation loop establishes complete issued
function maps, while retaining all old store objects. The exact helper effect
also records each function's canonical signature and source function index. -/
theorem function_staging_loop {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (seed inst : runtime.store.ModuleInst)
    (instanceIndex start : Usize)
    (startBound : start.val ≤ seed.module.module.env.func_type_indices.val.length)
    (changed : store = {before with funcs := store.funcs})
    (instChanged : inst = {seed with funcs := inst.funcs})
    (retained : StagedPrefix before store) (objectBound : objectCount store ≤ Usize.max)
    (typeBounds : ∀ idx ∈ seed.module.module.env.func_type_indices.val, idx.val < seed.types.length)
    (issued : ∀ address ∈ inst.funcs.val, address.index.val < store.funcs.length)
    (count : inst.funcs.length = seed.funcs.length + start.val)
    (capacity : seed.funcs.length + seed.module.module.env.func_type_indices.val.length ≤ Usize.max) :
    runtime.store.instantiate.Store.prepare_instance_loop4 memory allocator store (.Ok ()) start inst instanceIndex
      ⦃ out => ∃ after next status, out = typeParts after status next ∧
        after = {before with funcs := after.funcs} ∧ next = {seed with funcs := next.funcs} ∧
        StagedPrefix before after ∧ objectCount after ≤ Usize.max ∧
        (∀ address ∈ next.funcs.val, address.index.val < after.funcs.length) ∧
        (status = .Ok () → next.funcs.length = seed.funcs.length + seed.module.module.env.func_type_indices.val.length) ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop4
  apply loop.spec_decr_nat (fun state => seed.module.module.env.func_type_indices.val.length - state.2.2.1.val)
    (fun state => state.1 = {before with funcs := state.1.funcs} ∧
      state.2.2.2 = {seed with funcs := state.2.2.2.funcs} ∧ StagedPrefix before state.1 ∧
      objectCount state.1 ≤ Usize.max ∧
      (∀ address ∈ state.2.2.2.funcs.val, address.index.val < state.1.funcs.length) ∧
      state.2.2.1.val ≤ seed.module.module.env.func_type_indices.val.length ∧
      (state.2.1 = .Ok () → state.2.2.2.funcs.length = seed.funcs.length + state.2.2.1.val))
  · rintro ⟨current, status, index, currentInst⟩ ⟨currentChanged, mapChanged, prefixStore, bound, currentIssued, indexBound, counting⟩
    dsimp only at currentChanged mapChanged prefixStore bound currentIssued indexBound counting ⊢
    have source : currentInst.module = seed.module := by
      have eq := congrArg runtime.store.ModuleInst.module mapChanged
      exact eq
    have types : currentInst.types = seed.types := by
      have eq := congrArg runtime.store.ModuleInst.types mapChanged
      exact eq
    unfold runtime.store.instantiate.Store.prepare_instance_loop4.body
    simp only [runtime.compiler.ExecutableModule.env, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.func_type_indices, source, bind_ok]
    split
    · rename_i more
      have within : index.val < seed.module.module.env.func_type_indices.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, currentInst, .Err error, by simp [typeParts, source], currentChanged,
          mapChanged, prefixStore, bound, currentIssued, by simp⟩
      | Ok value =>
        cases value
        have size := counting rfl
        have actualBound : index.val < currentInst.module.module.env.func_type_indices.val.length := by simpa only [source] using within
        have typeBound : currentInst.module.module.env.func_type_indices.val[index.val].val < currentInst.types.val.length := by
          simpa only [source, types] using typeBounds _ (List.getElem_mem within)
        have room : currentInst.funcs.length < Usize.max := by omega
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step with add_instance_function_effect memory allocator law current currentInst instanceIndex index
          bound actualBound typeBound room as ⟨status, after, nextInst, effect⟩
        obtain ⟨afterChanged, nextChanged, prefixNext, nextBound, _⟩ := effect.context bound
        have afterExact : after = {before with funcs := after.funcs} := by
          calc
            after = {current with funcs := after.funcs} := afterChanged
            _ = _ := by rw [currentChanged]
        have nextExact : nextInst = {seed with funcs := nextInst.funcs} := by
          calc
            nextInst = {currentInst with funcs := nextInst.funcs} := nextChanged
            _ = _ := by rw [mapChanged]
        step as ⟨next, increment⟩
        refine ⟨afterExact, nextExact, prefixStore.trans prefixNext, nextBound,
          effect.issued currentIssued, ?_, ?_, ?_⟩
        · omega
        · intro success
          have appended := effect.count success
          dsimp only at appended
          omega
        · omega
    · rename_i stopped
      have atEnd : index.val = seed.module.module.env.func_type_indices.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      refine ⟨current, currentInst, status, by simp [typeParts, source], currentChanged,
        mapChanged, prefixStore, bound, currentIssued, ?_⟩
      intro success
      simpa only [atEnd] using counting success
  · exact ⟨changed, instChanged, retained, objectBound, issued, startBound, fun _ => count⟩

end Itasca.Runtime.Store

end

end
