import Itasca.Runtime.Store.Definitions
import ItascaRust.Funs
import Itasca.Runtime.Representation.Store
import Itasca.Runtime.Interp.Relations.SourceClosure
import Itasca.Runtime.Interp.Relations.SlotsAndDefaults
import Itasca.Runtime.Store.Preparation.Staging
import Itasca.Runtime.Store.Invariant.FunctionStaging
import Itasca.Module.Const.Parser
import Itasca.Runtime.Compiler.Local.Initializer.SegmentEmissionContracts
import Itasca.Runtime.Platform.Laws
import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Compiler.Local.Initializer
import Itasca.Runtime.Store.Invariant.Typing

/-!
Proofs for Runtime / Store / Initialization.

This module collects SegmentOperations, DataSegments.
Each section documents its contracts and consumers.
-/

/-! ## SegmentOperations -/

section

open Itasca.Representation

/-!
# Segment Operations

Element and data segment loops retain their accounting, mappings and initialization certificates.
-/

/-! ## SegmentAccounting -/

section

/-! Every stored element/data segment is retained by one instance map. This
reachable-store invariant supplies allocation bounds not implied by Shape
alone, which permits unreferenced raw segment entries. -/
namespace Itasca.Store
open Aeneas Aeneas.Std

theorem SegmentAccounting.element_bound {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} (accounted : SegmentAccounting store) (shape : Shape view store) :
    store.elems.length ≤ store.instance_items.val := by
  rw [accounted.elements, shape.instanceAccounting]
  suffices ∀ values : List runtime.store.ModuleInst,
      (values.map fun inst => inst.elems.length).sum ≤ (values.map instanceItems).sum by exact this _
  intro values
  induction values with
  | nil => simp
  | cons head tail ih => simp only [List.map_cons, List.sum_cons]; unfold instanceItems at *; omega

theorem SegmentAccounting.data_bound {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} (accounted : SegmentAccounting store) (shape : Shape view store) :
    store.datas.length ≤ store.instance_items.val := by
  rw [accounted.datas, shape.instanceAccounting]
  suffices ∀ values : List runtime.store.ModuleInst,
      (values.map fun inst => inst.datas.length).sum ≤ (values.map instanceItems).sum by exact this _
  intro values
  induction values with
  | nil => simp
  | cons head tail ih => simp only [List.map_cons, List.sum_cons]; unfold instanceItems at *; omega

/-- Public non-instantiation operations preserve segment accounting whenever
they leave the segment vectors and instance maps unchanged. -/
theorem SegmentAccounting.preserve {M : Type} {before after : runtime.store.Store M}
    (accounted : SegmentAccounting before) (elements : after.elems = before.elems)
    (datas : after.datas = before.datas) (instances : after.instances = before.instances) :
    SegmentAccounting after := by
  constructor
  · simpa only [elements, instances] using accounted.elements
  · simpa only [datas, instances] using accounted.datas

/-- An exact per-instance segment-map update accounts for the corresponding
append to each store segment vector. -/
theorem SegmentAccounting.update_instance {M : Type} {before after : runtime.store.Store M}
    (accounted : SegmentAccounting before) (index : Usize) (old next : runtime.store.ModuleInst)
    (found : before.instances.val[index.val]? = some old)
    (instances : after.instances = before.instances.set index next)
    (elementCount dataCount : Nat)
    (elements : after.elems.length = before.elems.length + elementCount)
    (datas : after.datas.length = before.datas.length + dataCount)
    (elementMap : next.elems.length = old.elems.length + elementCount)
    (dataMap : next.datas.length = old.datas.length + dataCount) : SegmentAccounting after := by
  have bound : index.val < before.instances.val.length := (List.getElem?_eq_some_iff.mp found).1
  have read : before.instances.val[index.val] = old :=
    Option.some.inj ((List.getElem?_eq_getElem bound).symm.trans found)
  constructor
  · rw [elements, accounted.elements, instances, alloc.vec.Vec.set_val_eq, List.map_set, elementMap]
    have effect := sum_set_add (before.instances.val.map fun inst => inst.elems.length) index.val elementCount
      (by simpa using bound)
    simpa only [List.getElem_map, read] using effect.symm
  · rw [datas, accounted.datas, instances, alloc.vec.Vec.set_val_eq, List.map_set, dataMap]
    have effect := sum_set_add (before.instances.val.map fun inst => inst.datas.length) index.val dataCount
      (by simpa using bound)
    simpa only [List.getElem_map, read] using effect.symm

/-- Publishing a new instance with its segment vectors preserves exact segment
accounting, including the empty-map instance staged before initialization. -/
theorem SegmentAccounting.append_instance {M : Type} {before after : runtime.store.Store M}
    (accounted : SegmentAccounting before) (inst : runtime.store.ModuleInst)
    (instances : after.instances.val = before.instances.val ++ [inst])
    (elements : after.elems.length = before.elems.length + inst.elems.length)
    (datas : after.datas.length = before.datas.length + inst.datas.length) : SegmentAccounting after := by
  constructor
  · simp [elements, instances, accounted.elements]
  · simp [datas, instances, accounted.datas]

end Itasca.Store

end

/-! ## SegmentCounts -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

theorem SegmentCounts.accounting {M : Type} {before after : runtime.store.Store M}
    (counts : SegmentCounts before after) (instances : after.instances = before.instances)
    (accounted : SegmentAccounting before) : SegmentAccounting after := by
  constructor
  · simpa only [counts.elements,instances] using accounted.elements
  · simpa only [counts.datas,instances] using accounted.datas

end Itasca.Store

end

/-! ## Initializer -/

section

/-! The real instantiation constant-expression wrapper is read-only and total
under compiler syntax, resolved source operands, and the reference-index bound
needed by the public primitive decoder. These premises mention no execution
result or termination property. -/
namespace Itasca.Store
open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem eval_const_effect (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) (words : List U64)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hc : inst.module.functions.val[function.val]? = some code)
    (compiled : Compiler.InitializerCode code expr ty)
    (resolved : Interp.InitializerResolution store inst expr ty words)
    (referenceBound : ty = .FuncRef ∨ ty = .ExternRef → ((words[0]?).getD 0#u64).val ≤ Usize.max) :
    runtime.interp.eval_const memory hooks floats allocator store platform instIndex function ty
      ⦃ out => out.2.1 = store ∧ out.2.2 = platform ∧
        ∀ value, out.1 = .Ok value → Representation.rawType value = ty ∧
          Representation.sourceValue value = decodeWords ty ((words[0]?).getD 0#u64) ((words[1]?).getD 0#u64) ⦄ := by
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

def initializerGlobal (ty : Itasca.wasm_types.ValueType) (words : List U64) : runtime.store.GlobalInst :=
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
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) (words : List U64)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hc : inst.module.functions.val[function.val]? = some code)
    (compiled : Compiler.InitializerCode code expr ty)
    (resolved : Interp.InitializerResolution store inst expr ty words)
    (bindings : InitializerBindings store inst) :
    runtime.interp.eval_const memory hooks floats allocator store platform instIndex function ty
      ⦃ out => out.2.1 = store ∧ out.2.2 = platform ∧
        ∀ value, out.1 = .Ok value → ValueInStore store value ∧ Representation.rawType value = ty ⦄ := by
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
        ⦃ result => ValueInStore store result ∧ Representation.rawType result = ty ⦄ :=
      WP.exists_imp_spec ⟨value, decoded, owned, hty⟩
    step with combined as ⟨actual, howned, htyped⟩
    simp [howned, htyped]

end Itasca.Store

end

/-! ## InitializerResolve -/

section

/-! Validator constant typing resolves to concrete initializer words using only
issued function maps and the linked imported-global prefix. -/
namespace Itasca.Store
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
    (valid : Itasca.Module.Constants.Valid inst.module.module.env expr ty)
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

end Itasca.Store

end

/-! ## BulkDrop -/

section

/-! Exact effects of the two segment-drop instructions, including ordinary
termination for issued local segment indices. -/
namespace Itasca.Store
open Aeneas Aeneas.Std

theorem bulk_data_drop {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (inst : runtime.store.ModuleInst) (data : U32) (address : Usize)
    (found : store.instances.val[instIndex.val]? = some inst)
    (mapped : inst.datas.val[data.val]? = some address)
    (issued : address.val < store.datas.length) :
    runtime.interp.bulk.execute memory store instIndex function base slots (.DataDrop data)
      ⦃ out => out = (.Ok (), {store with datas := store.datas.set address (⟨alloc.vec.Vec.new U8⟩)}) ⦄ := by
  simp only [runtime.interp.bulk.execute]
  step with Interp.vec_index_given store.instances instIndex inst found as ⟨actual, hactual⟩
  subst actual
  simp only [lift, bind_ok]
  step with Interp.vec_index_given inst.datas (UScalar.cast .Usize data) address
    (by simpa using mapped) as ⟨actual, hactual⟩
  subst actual
  step as ⟨segment, back, read, write⟩
  simp [write]

theorem bulk_element_drop {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (inst : runtime.store.ModuleInst) (elem : U32) (address : Usize)
    (found : store.instances.val[instIndex.val]? = some inst)
    (mapped : inst.elems.val[elem.val]? = some address)
    (issued : address.val < store.elems.length) :
    runtime.interp.bulk.execute memory store instIndex function base slots (.ElemDrop elem)
      ⦃ out => out = (.Ok (), {store with elems := store.elems.set address ({store.elems.val[address.val] with refs := alloc.vec.Vec.new U64})}) ⦄ := by
  simp only [runtime.interp.bulk.execute]
  step with Interp.vec_index_given store.instances instIndex inst found as ⟨actual, hactual⟩
  subst actual
  simp only [lift, bind_ok]
  step with Interp.vec_index_given inst.elems (UScalar.cast .Usize elem) address
    (by simpa using mapped) as ⟨actual, hactual⟩
  subst actual
  step as ⟨segment, back, read, write⟩
  simp [write, read]

end Itasca.Store

end

/-! ## BulkTableLoop -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- Copy from an independent element segment. The recursion records exactly the
left-to-right writes made by table.init. -/
def copySegment (before source : List U64) (dst src : Nat) : Nat → List U64
  | 0 => before
  | n + 1 => (copySegment before source dst src n).set (dst + n) source[src + n]!

theorem copy_segment_length (before source : List U64) (dst src count : Nat) :
    (copySegment before source dst src count).length = before.length := by
  induction count with
  | zero => rfl
  | succ n ih => simp only [copySegment, List.length_set, ih]

theorem table_init_loop (tables : alloc.vec.Vec runtime.store.TableInst)
    (instances : alloc.vec.Vec runtime.store.ModuleInst)
    (elements : alloc.vec.Vec runtime.store.ElemInst)
    (instIndex : Usize) (elemIndex : U32) (len : U64) (tableIndex : Usize)
    (dst src : core.ops.range.Range Usize) (inst : runtime.store.ModuleInst)
    (address : Usize) (segment : runtime.store.ElemInst) (table : runtime.store.TableInst)
    (found : instances.val[instIndex.val]? = some inst)
    (mapped : inst.elems.val[elemIndex.val]? = some address)
    (resolved : elements.val[address.val]? = some segment)
    (target : tables.val[tableIndex.val]? = some table)
    (sourceBound : src.start.val + len.val ≤ segment.refs.length)
    (targetBound : dst.start.val + len.val ≤ table.elements.length) :
    runtime.interp.bulk.execute_loop6 tables instances elements instIndex elemIndex len
      tableIndex dst src 0#usize ⦃ out => ∃ words,
        out = tables.set tableIndex {table with elements := words} ∧
        words.val = copySegment table.elements.val segment.refs.val dst.start.val src.start.val len.val ⦄ := by
  have tableBound : tableIndex.val < tables.length := (List.getElem?_eq_some_iff.mp target).1
  have tableRead : tables.val[tableIndex.val] = table := (List.getElem?_eq_some_iff.mp target).2
  have lengthBound : len.val ≤ Usize.max := by
    have h : segment.refs.length ≤ Usize.max := segment.refs.property
    omega
  have castLength := Interp.cast_usize_exact len lengthBound
  unfold runtime.interp.bulk.execute_loop6
  apply loop.spec_decr_nat (fun state => len.val - state.2.val)
    (fun state => state.2.val ≤ len.val ∧ ∃ words : alloc.vec.Vec U64,
      words.val = copySegment table.elements.val segment.refs.val dst.start.val src.start.val state.2.val ∧
      state.1 = tables.set tableIndex {table with elements := words})
  · rintro ⟨current, index⟩ ⟨indexBound, words, wordValues, currentEq⟩
    dsimp only at indexBound wordValues currentEq ⊢
    have wordLength : words.length = table.elements.length := by
      simpa only [alloc.vec.Vec.length] using congrArg List.length wordValues |>.trans
        (copy_segment_length _ _ _ _ _)
    have currentFound : current.val[tableIndex.val]? = some {table with elements := words} := by
      rw [currentEq]
      simp [alloc.vec.Vec.set_val_eq, tableBound]
    unfold runtime.interp.bulk.execute_loop6.body
    simp only [lift, bind_ok]
    split
    · rename_i more
      have less : index.val < len.val := by simpa only [UScalar.lt_equiv, castLength] using more
      step with Interp.vec_index_given instances instIndex inst found as ⟨actual, actualEq⟩
      subst actual
      step with Interp.vec_index_given inst.elems (UScalar.cast .Usize elemIndex) address
        (by simpa using mapped) as ⟨actual, actualEq⟩
      subst actual
      step with Interp.vec_index_given elements address segment resolved as ⟨actual, actualEq⟩
      subst actual
      have sourceInside : src.start.val + index.val < segment.refs.length := by omega
      have targetInside : dst.start.val + index.val < words.length := by omega
      have currentBound : tableIndex.val < current.length := by rw [currentEq]; simpa using tableBound
      step as ⟨sourcePosition, sourcePositionEq⟩
      step with Interp.vec_index_given segment.refs sourcePosition
        segment.refs.val[src.start.val + index.val]!
        (by simp [sourcePositionEq, sourceInside]) as ⟨value, valueEq⟩
      step as ⟨actualTable, tableBack, actualTableEq, tableBackEq⟩
      have actualTableSame : actualTable = {table with elements := words} := by
        have h := List.getElem?_eq_getElem currentBound
        rw [currentFound] at h
        exact actualTableEq.trans (Option.some.inj h).symm
      subst actualTable
      step as ⟨targetPosition, targetPositionEq⟩
      step as ⟨oldValue, wordsBack, oldValueEq, wordsBackEq⟩
      step as ⟨next, nextEq⟩
      refine ⟨?_, ⟨words.set targetPosition value, ?_, ?_⟩, ?_⟩
      · omega
      · simp only [alloc.vec.Vec.set_val_eq, wordValues, targetPositionEq, nextEq, copySegment]
        have sourceInside : src.start.val + index.val < segment.refs.val.length := by omega
        have valueSame : value = segment.refs.val[src.start.val + index.val]! := by
          exact valueEq
        rw [valueSame]
      · simp only [wordsBackEq, tableBackEq, currentEq]
        apply alloc.vec.Vec.ext
        simp [alloc.vec.Vec.set_val_eq, List.set_set]
      · omega
    · rename_i more
      have last : index.val = len.val := by
        have notMore : ¬ index.val < len.val := by simpa only [UScalar.lt_equiv, castLength] using more
        omega
      simp only [WP.spec_ok]
      exact ⟨words, currentEq, by simpa only [last] using wordValues⟩
  · refine ⟨by simp, table.elements, rfl, ?_⟩
    have same : {table with elements := table.elements} = table := by cases table; rfl
    rw [same, ← tableRead, vec_set_current tables tableIndex tableBound]

end Itasca.Store

end

/-! ## BulkTable -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

theorem bulk_zero_add (value : Usize) : (0#usize + value : Result Usize) = .ok value := by
  have spec : (0#usize + value : Result Usize) ⦃ out => out = value ⦄ := by
    step as ⟨out, equal⟩
    scalar_tac
  obtain ⟨out, call, rfl⟩ := WP.spec_imp_exists spec
  exact call

theorem bulk_zero_cast : UScalar.cast .Usize 0#u32 = 0#usize := by scalar_tac

/-- The encoded i32 operand used by a bulk instruction. -/
abbrev bulkWord (word : U64) : U64 := UScalar.cast .U64 (UScalar.cast .U32 word)

def TableInitializationEffect {M : Type} (store : runtime.store.Store M)
    (tableIndex : Usize) (table : runtime.store.TableInst) (segment : runtime.store.ElemInst)
    (destination source count : U64)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M) : Prop :=
  if destination.val + count.val ≤ table.elements.length ∧ source.val + count.val ≤ segment.refs.length then
    ∃ words, out = (.Ok (), {store with tables := store.tables.set tableIndex {table with elements := words}}) ∧
      words.val = copySegment table.elements.val segment.refs.val destination.val source.val count.val
  else out = (.Err (.Trap .TableOutOfBounds), store)

theorem bulk_table_init {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (store : runtime.store.Store M) (instIndex function : Usize) (slots : Slice U64)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (entry element tableId : U32) (address : Usize) (tableAddress : runtime.TableAddr)
    (table : runtime.store.TableInst) (segment : runtime.store.ElemInst)
    (destination source count : U64)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some code)
    (descriptor : code.indirect.val[entry.val]? = some (element, tableId))
    (mapped : inst.elems.val[element.val]? = some address)
    (resolved : store.elems.val[address.val]? = some segment)
    (tableMapped : inst.tables.val[tableId.val]? = some tableAddress)
    (target : store.tables.val[tableAddress.index.val]? = some table)
    (destinationSlot : slots.val[0]? = some destination)
    (sourceSlot : slots.val[1]? = some source)
    (countSlot : slots.val[2]? = some count) :
    runtime.interp.bulk.execute memory store instIndex function 0#usize slots (.TableInit 0#u32 entry)
      ⦃ out => TableInitializationEffect store tableAddress.index table segment
        (bulkWord destination) (bulkWord source) (bulkWord count) out ⦄ := by
  simp only [runtime.interp.bulk.execute]
  step with Interp.vec_index_given store.instances instIndex inst found as ⟨actual, actualEq⟩
  subst actual
  step with Interp.vec_index_given inst.module.functions function code functionFound as ⟨actual, actualEq⟩
  subst actual
  simp only [lift, bind_ok]
  step with Interp.vec_index_given code.indirect (UScalar.cast .Usize entry) (element, tableId)
    (by simpa using descriptor) as ⟨a, b, aEq, bEq⟩
  subst a b
  have read0 := Compiler.initializer_slice_index slots 0#usize destination destinationSlot
  have read1 := Compiler.initializer_slice_index slots 1#usize source sourceSlot
  have read2 := Compiler.initializer_slice_index slots 2#usize count countSlot
  simp only [bulk_zero_cast, bulk_zero_add, bind_ok, read0, read1, read2]
  step with Interp.vec_index_given inst.tables (UScalar.cast .Usize tableId) tableAddress
    (by simpa using tableMapped) as ⟨actual, actualEq⟩
  subst actual
  step with Interp.vec_index_given store.tables tableAddress.index table target as ⟨actual, actualEq⟩
  subst actual
  step with Interp.range_effect (bulkWord destination) (bulkWord count) (alloc.vec.Vec.len table.elements)
    .TableOutOfBounds as ⟨result, rangeEffect⟩
  by_cases fitsTarget : (bulkWord destination).val + (bulkWord count).val ≤ table.elements.length
  · change (if (bulkWord destination).val + (bulkWord count).val ≤ table.elements.length then _ else _) at rangeEffect
    rw [if_pos fitsTarget] at rangeEffect
    obtain ⟨dst, rfl, dstStart, dstEnd⟩ := rangeEffect
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with Interp.vec_index_given inst.elems (UScalar.cast .Usize element) address
      (by simpa using mapped) as ⟨actual, actualEq⟩
    subst actual
    step with Interp.vec_index_given store.elems address segment resolved as ⟨actual, actualEq⟩
    subst actual
    step with Interp.range_effect (bulkWord source) (bulkWord count) (alloc.vec.Vec.len segment.refs)
      .TableOutOfBounds as ⟨result, rangeEffect⟩
    by_cases fitsSource : (bulkWord source).val + (bulkWord count).val ≤ segment.refs.length
    · change (if (bulkWord source).val + (bulkWord count).val ≤ segment.refs.length then _ else _) at rangeEffect
      rw [if_pos fitsSource] at rangeEffect
      obtain ⟨src, rfl, srcStart, srcEnd⟩ := rangeEffect
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with table_init_loop store.tables store.instances store.elems instIndex element (bulkWord count)
        tableAddress.index dst src inst address segment table found mapped resolved target
        (by simpa only [srcStart] using fitsSource) (by simpa only [dstStart] using fitsTarget)
        as ⟨tables, words, tablesEq, valuesEq⟩
      simp only [TableInitializationEffect, fitsSource, fitsTarget, and_self, ↓reduceIte]
      exact ⟨words, by rw [tablesEq], by simpa only [srcStart, dstStart] using valuesEq⟩
    · change (if (bulkWord source).val + (bulkWord count).val ≤ segment.refs.length then _ else _) at rangeEffect
      rw [if_neg fitsSource] at rangeEffect
      rw [rangeEffect]
      simp_all [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        TableInitializationEffect]
  · change (if (bulkWord destination).val + (bulkWord count).val ≤ table.elements.length then _ else _) at rangeEffect
    rw [if_neg fitsTarget] at rangeEffect
    rw [rangeEffect]
    simp_all [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      TableInitializationEffect]

end Itasca.Store

end

/-! ## BulkMemory -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

def MemoryInitializationEffect {M : Type} (view : M → Slice U8) (store : runtime.store.Store M)
    (memoryIndex : Usize) (memory : runtime.store.MemInst M) (segment : runtime.store.DataInst)
    (destination source count : U64)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M) : Prop :=
  if destination.val + count.val ≤ (view memory.buf).length ∧ source.val + count.val ≤ segment.bytes.length then
    ∃ buffer, out = (.Ok (), {store with memories := store.memories.set memoryIndex {memory with buf := buffer}}) ∧
      (view buffer).val = (view memory.buf).val.setSlice! destination.val
        (segment.bytes.val.slice source.val (source.val + count.val))
  else out = (.Err (.Trap .MemoryOutOfBounds), store)

theorem bulk_memory_init {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws ops view)
    (store : runtime.store.Store M) (instIndex function : Usize) (slots : Slice U64)
    (inst : runtime.store.ModuleInst) (data : U32) (address : Usize) (memoryAddress : runtime.MemoryAddr)
    (memory : runtime.store.MemInst M) (segment : runtime.store.DataInst)
    (destination source count : U64)
    (found : store.instances.val[instIndex.val]? = some inst)
    (mapped : inst.datas.val[data.val]? = some address)
    (resolved : store.datas.val[address.val]? = some segment)
    (memoryMapped : inst.memories.val[0]? = some memoryAddress)
    (target : store.memories.val[memoryAddress.index.val]? = some memory)
    (destinationSlot : slots.val[0]? = some destination)
    (sourceSlot : slots.val[1]? = some source)
    (countSlot : slots.val[2]? = some count) :
    runtime.interp.bulk.execute ops store instIndex function 0#usize slots (.MemoryInit 0#u32 data)
      ⦃ out => MemoryInitializationEffect view store memoryAddress.index memory segment
        (bulkWord destination) (bulkWord source) (bulkWord count) out ⦄ := by
  have read0 := Compiler.initializer_slice_index slots 0#usize destination destinationSlot
  have read1 := Compiler.initializer_slice_index slots 1#usize source sourceSlot
  have read2 := Compiler.initializer_slice_index slots 2#usize count countSlot
  simp only [runtime.interp.bulk.execute, lift, bind_ok, bulk_zero_cast, bulk_zero_add,
    read0, read1, read2]
  step with Interp.vec_index_given store.instances instIndex inst found as ⟨actual, actualEq⟩
  subst actual
  step with Interp.vec_index_given inst.memories 0#usize memoryAddress memoryMapped as ⟨actual, actualEq⟩
  subst actual
  step with Interp.vec_index_given store.memories memoryAddress.index memory target as ⟨actual, actualEq⟩
  subst actual
  rw [laws.read, bind_ok]
  step with Interp.range_effect (bulkWord destination) (bulkWord count) (Slice.len (view memory.buf))
    .MemoryOutOfBounds as ⟨result, rangeEffect⟩
  by_cases fitsTarget : (bulkWord destination).val + (bulkWord count).val ≤ (view memory.buf).length
  · change (if (bulkWord destination).val + (bulkWord count).val ≤ (view memory.buf).length then _ else _) at rangeEffect
    rw [if_pos fitsTarget] at rangeEffect
    obtain ⟨dst, rfl, dstStart, dstEnd⟩ := rangeEffect
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with Interp.vec_index_given inst.datas (UScalar.cast .Usize data) address
      (by simpa using mapped) as ⟨actual, actualEq⟩
    subst actual
    step with Interp.vec_index_given store.datas address segment resolved as ⟨actual, actualEq⟩
    subst actual
    step with Interp.range_effect (bulkWord source) (bulkWord count) (alloc.vec.Vec.len segment.bytes)
      .MemoryOutOfBounds as ⟨result, rangeEffect⟩
    by_cases fitsSource : (bulkWord source).val + (bulkWord count).val ≤ segment.bytes.length
    · change (if (bulkWord source).val + (bulkWord count).val ≤ segment.bytes.length then _ else _) at rangeEffect
      rw [if_pos fitsSource] at rangeEffect
      obtain ⟨src, rfl, srcStart, srcEnd⟩ := rangeEffect
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have memoryBound : memoryAddress.index.val < store.memories.length :=
        (List.getElem?_eq_some_iff.mp target).1
      have memoryRead : store.memories.val[memoryAddress.index.val] = memory :=
        (List.getElem?_eq_some_iff.mp target).2
      step as ⟨actualMemory, memoryBack, actualMemoryEq, memoryBackEq⟩
      have sameMemory : actualMemory = memory := actualMemoryEq.trans memoryRead
      rw [sameMemory]
      obtain ⟨back, write, viewBack⟩ := laws.write memory.buf
      rw [write, bind_ok]
      have dstOrder : dst.start ≤ dst.end := by scalar_tac
      have dstBound : dst.end.val ≤ (view memory.buf).length := by omega
      have srcOrder : src.start ≤ src.end := by scalar_tac
      have srcBound : src.end.val ≤ segment.bytes.length := by omega
      step as ⟨targetSlice, targetBack, targetValues, targetLength, targetBackEq⟩
      step as ⟨sourceSlice, sourceValues, sourceLength⟩
      have sameLength : targetSlice.length = sourceSlice.length := by omega
      step as ⟨copied, copiedEq⟩
      subst copied
      simp only [MemoryInitializationEffect, fitsSource, fitsTarget, and_self, ↓reduceIte]
      refine ⟨back (targetBack sourceSlice), ?_, ?_⟩
      · simp only [memoryBackEq]
      · rw [targetBackEq, viewBack _ (by simp)]
        rw [Slice.setSlice!_val, sourceValues, dstStart, srcStart, srcEnd]
    · change (if (bulkWord source).val + (bulkWord count).val ≤ segment.bytes.length then _ else _) at rangeEffect
      rw [if_neg fitsSource] at rangeEffect
      rw [rangeEffect]
      simp_all [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        MemoryInitializationEffect]
  · change (if (bulkWord destination).val + (bulkWord count).val ≤ (view memory.buf).length then _ else _) at rangeEffect
    rw [if_neg fitsTarget] at rangeEffect
    rw [rangeEffect]
    simp_all [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      MemoryInitializationEffect]

end Itasca.Store

end

/-! ## ElementLoop -/

section

/-! Finite preparation of element initializer values. Each input certificate
connects an actual source expression and retained synthetic function; no
execution premise is accepted. The loop leaves the store and platform intact. -/
namespace Itasca.Store
open Aeneas Aeneas.Std

def ElementInitializers {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (index : Usize) (segment : Itasca.metadata.Element) : Prop :=
  ∃ functions : alloc.vec.Vec Usize,
    inst.module.element_initializers.val[index.val]? = some functions ∧
    ∀ j : Usize, j.val < segment.init.length →
      ∃ expr function code words,
        segment.init.val[j.val]? = some expr ∧ functions.val[j.val]? = some function ∧
        inst.module.functions.val[function.val]? = some code ∧
        Compiler.InitializerCode code expr (elementValueType segment.elem) ∧
        Interp.InitializerResolution store inst expr (elementValueType segment.elem) words

private theorem elem_value_type_eq (ty : Itasca.wasm_types.ElemType) :
    wasm_types.ElemType.value_type ty = .ok (elementValueType ty) := by cases ty <;> rfl

private theorem encode_push {M : Type} (store : runtime.store.Store M)
    (values : alloc.vec.Vec U64) (value : runtime.Value) (owned : ValueInStore store value)
    (room : values.length < Usize.max) :
    (do let (lo, _) ← runtime.value.encode value
        let next ← alloc.vec.Vec.push values lo
        .ok (next, (core.result.Result.Ok () : core.result.Result Unit runtime.ExecError)))
      ⦃ out => out.1.length = values.length + 1 ∧ out.2 = .Ok () ⦄ := by
  step with Representation.encode_value_spec value store.id owned.1 as ⟨pair, hencoded⟩
  rcases pair with ⟨lo, high⟩
  step as ⟨next, hnext⟩
  simp [alloc.vec.Vec.length, hnext]

theorem element_initializers_loop {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex index length : Usize)
    (inst : runtime.store.ModuleInst) (segment : Itasca.metadata.Element)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (helem : inst.module.module.env.elements.val[index.val]? = some segment)
    (hlength : length.val = segment.init.length)
    (certificates : ElementInitializers store inst index segment)
    (bindings : InitializerBindings store inst)
    (values : alloc.vec.Vec U64) (j : Usize) (status : core.result.Result Unit runtime.ExecError)
    (hvalues : values.length ≤ j.val) (hj : j.val ≤ length.val) :
    runtime.store.instantiate.Store.add_instance_element_loop memory hooks floats allocator store platform
      instIndex index length values j status ⦃ out =>
        out.1 = store ∧ out.2.1 = platform ∧ out.2.2.1.length ≤ length.val ⦄ := by
  unfold runtime.store.instantiate.Store.add_instance_element_loop
  apply loop.spec_decr_nat (fun p => length.val - p.2.2.2.1.val)
    (fun p => p.1 = store ∧ p.2.1 = platform ∧
      p.2.2.1.length ≤ p.2.2.2.1.val ∧ p.2.2.2.1.val ≤ length.val)
  · rintro ⟨current, host, vals, k, state⟩ ⟨hcurrent, hhost, hvals, hk⟩
    dsimp only at hcurrent hhost hvals hk ⊢
    subst current host
    change vals.val.length ≤ k.val at hvals
    unfold runtime.store.instantiate.Store.add_instance_element_loop.body
    split
    · rename_i more
      have hmore : k.val < length.val := by scalar_tac
      cases state with
      | Err error =>
        simp [core.result.Result.is_ok]
        omega
      | Ok unit =>
        cases unit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        obtain ⟨functions, mapping, certificates⟩ := certificates
        obtain ⟨expr, function, code, words, hexpr, hfunction, hcode, compiled, resolved⟩ :=
          certificates k (by omega)
        step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
        subst found
        step with Interp.vec_index_given inst.module.element_initializers index functions mapping
          as ⟨found, hfound⟩
        subst found
        step with Interp.vec_index_given functions k function hfunction as ⟨found, hfound⟩
        subst found
        simp only [runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Env.impl.elements, bind_ok]
        step with Itasca.Representation.slice_index_given inst.module.module.env.elements.deref index segment
          (by simpa [alloc.vec.Vec.deref] using helem) as ⟨found, hfound⟩
        subst found
        rw [elem_value_type_eq, bind_ok]
        step with eval_const_owned memory hooks floats allocator law store platform instIndex function
          inst code expr (elementValueType segment.elem) words hi hcode compiled resolved bindings
          as ⟨result, after, host', hs, hp, hvalue⟩
        subst after host'
        cases result with
        | Err error =>
          step as ⟨next, hnext⟩
          change vals.val.length ≤ next.val ∧ next.val ≤ length.val ∧ length.val - next.val < length.val - k.val
          exact ⟨by omega, by omega, by omega⟩
        | Ok value =>
          obtain ⟨owned, typed⟩ := hvalue value rfl
          have room : vals.length < Usize.max := by scalar_tac
          apply WP.spec_bind (encode_push store vals value owned room)
          rintro ⟨pushed, nextStatus⟩ ⟨hpush, hstatus⟩
          step as ⟨next, hnext⟩
          refine ⟨?_, by omega, by omega⟩
          rw [hpush]
          change vals.val.length + 1 ≤ next.val
          omega
    · have hstop : length.val ≤ k.val := by scalar_tac
      simp only [WP.spec_ok]
      simp only [true_and]
      change vals.val.length ≤ length.val
      omega
  · exact ⟨rfl, rfl, hvalues, hj⟩

end Itasca.Store

end

end

/-! ## DataSegments -/

section

/-!
Proofs for Runtime / Store / Initialization.

This module collects Data, BulkInitialization.
Each section documents its contracts and consumers.
-/

/-! ## Data -/

section

open Itasca.Representation

/-! ## InitializerSource -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std Itasca

private theorem eval_literal (s : _root_.store) (f : frame) (instruction : instr) (value : val)
    (storeWf : wf_store s) (frameWf : wf_frame f)
    (valueWf : wf_val value) (same : admininstr_instr instruction = admininstr_val value) :
    Eval_expr ⟨s, f⟩ [instruction] ⟨s, f⟩ [value] := by
  have wf := Itasca.Spec.wf_config_vals (vs := [value]) storeWf frameWf (by simpa [Forall] using valueWf)
  simp only [WebAssembly.vals, List.map_cons, List.map_nil] at wf
  apply Eval_expr.mk_Eval_expr
  · simpa only [Map, List.map_cons, List.map_nil, same] using Steps.refl _ _ wf
  · simpa only [Map, List.map_cons, List.map_nil, same] using wf
  · exact wf

private theorem eval_read (s : _root_.store) (f : frame) (instruction : instr) (value : val)
    (storeWf : wf_store s) (frameWf : wf_frame f)
    (instructionWf : wf_instr instruction) (valueWf : wf_val value)
    (read : Step_read ⟨⟨s, f⟩, [admininstr_instr instruction]⟩ [admininstr_val value]) :
    Eval_expr ⟨s, f⟩ [instruction] ⟨s, f⟩ [value] := by
  have before := Itasca.Spec.wf_config_make storeWf frameWf
    (show Forall wf_admininstr [admininstr_instr instruction] by
      simpa [Forall] using Itasca.Spec.wf_admininstr_instr instructionWf)
  have after := Itasca.Spec.wf_config_make storeWf frameWf
    (show Forall wf_admininstr [admininstr_val value] by
      simpa [Forall] using Itasca.Spec.wf_admininstr_val valueWf)
  exact .mk_Eval_expr _ _ _ _
    (.trans _ _ _ _ _ _ (.read _ _ _ read before after) (.refl _ _ after) before after after) before after

private theorem float_value_32 (bits : U32) :
    WebAssembly.Builtins.floatOfBits 32 bits.val = Spec.Constants.floatValue 23 8 bits.val := by
  have bound : bits.val < 2^32 := by scalar_tac
  have sign : (bits.val / 2^31) % 2 = 0 ↔ bits.val < 2^31 := by omega
  norm_num at sign
  simp [WebAssembly.Builtins.floatOfBits, Spec.Constants.floatValue, fun_M, E, signif, expon,
    WebAssembly.Builtins.floatBias, sign]

private theorem float_value_64 (bits : U64) :
    WebAssembly.Builtins.floatOfBits 64 bits.val = Spec.Constants.floatValue 52 11 bits.val := by
  have bound : bits.val < 2^64 := by scalar_tac
  have sign : (bits.val / 2^63) % 2 = 0 ↔ bits.val < 2^63 := by omega
  norm_num at sign
  simp [WebAssembly.Builtins.floatOfBits, Spec.Constants.floatValue, fun_M, E, signif, expon,
    WebAssembly.Builtins.floatBias, sign]

/-- Resolved initializer operands evaluate under the generated source rules.
This connects the runtime's exact literal/global/reference words to Eval_expr,
without a source execution premise. -/
theorem initializer_resolution_source_in_state {M : Type}
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (expression : wasm_types.ConstExpr) (ty : wasm_types.ValueType) (words : List U64)
    (resolved : Interp.InitializerResolution store inst expression ty words)
    (sourceStore : _root_.store) (sourceInstance : moduleinst)
    (functions : sourceInstance.FUNCS = inst.funcs.val.map (fun address => address.index.val))
    (globals : ∀ index address global, expression = .GlobalGet index →
      inst.globals.val[index.val]? = some address → store.globals.val[address.index.val]? = some global →
      fun_global ⟨sourceStore, ⟨[], sourceInstance⟩⟩ (.mk_uN index.val) = decodeGlobal global)
    (storeWf : wf_store sourceStore)
    (frameWf : wf_frame ⟨[], sourceInstance⟩) :
    Eval_expr ⟨sourceStore, ⟨[], sourceInstance⟩⟩
      (Module.Constants.expression expression)
      ⟨sourceStore, ⟨[], sourceInstance⟩⟩
      [decodeWords ty ((words[0]?).getD 0#u64) ((words[1]?).getD 0#u64)] := by
  have outputWf := decode_words_wf ty ((words[0]?).getD 0#u64) ((words[1]?).getD 0#u64)
  have inputWf := Module.Constants.instruction_wf expression
  cases resolved with
  | i32 value =>
    apply eval_literal _ _ _ _ storeWf frameWf outputWf
    simp only [Module.Constants.instruction, Spec.i32Const, admininstr_instr, admininstr_val,
      decodeWords, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Option.getD_some, Option.getD_none]
    congr 3
    have modulus : (value.val % 4294967296).toNat < 4294967296 := by
      have bound := Int.emod_lt_of_pos value.val (by decide : (0 : Int) < 4294967296)
      omega
    simp [UScalar.cast_val_eq, IScalar.hcast_val_eq, Nat.mod_eq_of_lt modulus]
  | i64 value =>
    apply eval_literal _ _ _ _ storeWf frameWf outputWf
    simp [Module.Constants.instruction, Spec.Constants.i64, admininstr_instr, admininstr_val,
      decodeWords, IScalar.hcast_val_eq]
  | f32 bits =>
    apply eval_literal _ _ _ _ storeWf frameWf outputWf
    have exactBits : (UScalar.cast .U64 bits).val % 2^32 = bits.val := by scalar_tac
    simp [Module.Constants.instruction, Spec.Constants.f32, admininstr_instr, admininstr_val,
      decodeWords, exactBits, float_value_32]
  | f64 bits =>
    apply eval_literal _ _ _ _ storeWf frameWf outputWf
    simp [Module.Constants.instruction, Spec.Constants.f64, admininstr_instr, admininstr_val,
      decodeWords, float_value_64]
  | vector lo hi =>
    apply eval_literal _ _ _ _ storeWf frameWf outputWf
    simp [Module.Constants.instruction, admininstr_instr, admininstr_val, decodeWords, Nat.mul_comm]
  | nullFunc =>
    apply eval_literal _ _ _ _ storeWf frameWf outputWf
    rfl
  | nullExtern =>
    apply eval_literal _ _ _ _ storeWf frameWf outputWf
    rfl
  | func index address reference lookup encoded =>
    have value : decodeWords .FuncRef reference 0#u64 = .REF_FUNC_ADDR address.index.val := by
      simp [decodeWords, decodeRef, encoded, refVal]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Option.getD_some, Option.getD_none] at outputWf ⊢
    rw [value] at outputWf ⊢
    apply eval_read _ _ _ _ storeWf frameWf inputWf outputWf
    have bound := (List.getElem?_eq_some_iff.mp lookup).1
    have fetched : (fun_funcaddr ⟨sourceStore, ⟨[], sourceInstance⟩⟩)[index.val]! = address.index.val := by
      simp [fun_funcaddr, functions, List.getElem!_eq_getElem?_getD, List.getElem?_map, lookup]
    simpa only [Module.Constants.instruction, admininstr_instr, admininstr_val, proj_uN_0, fetched] using
      (Step_read.ref_func ⟨sourceStore, ⟨[], sourceInstance⟩⟩ (.mk_uN index.val)
        (by simpa [fun_funcaddr, functions, proj_uN_0] using bound)
        (Itasca.Spec.wf_config_make storeWf frameWf (by
          simpa [Forall, Module.Constants.instruction, admininstr_instr] using Itasca.Spec.wf_admininstr_instr inputWf))
        (by simp only [proj_uN_0, fetched]; constructor))
  | global ty index address global lookup found typed scalar =>
    have value : decodeWords ty global.lo 0#u64 = (decodeGlobal global).VALUE := by
      cases ty <;> simp_all [decodeGlobal, decodeWords]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Option.getD_some, Option.getD_none] at outputWf ⊢
    rw [value] at outputWf ⊢
    apply eval_read _ _ _ _ storeWf frameWf inputWf outputWf
    have fetched : fun_global ⟨sourceStore, ⟨[], sourceInstance⟩⟩ (.mk_uN index.val) = decodeGlobal global := by
      exact globals index address global rfl lookup found
    simpa only [Module.Constants.instruction, admininstr_instr, fetched] using
      (Step_read.global_get ⟨sourceStore, ⟨[], sourceInstance⟩⟩ (.mk_uN index.val)
        (Itasca.Spec.wf_config_make storeWf frameWf (by simpa [Forall, Module.Constants.instruction, admininstr_instr] using Itasca.Spec.wf_admininstr_instr inputWf)))
  | global2 index address global lookup found typed =>
    have value : decodeWords .V128 global.lo global.hi = (decodeGlobal global).VALUE := by
      simp [decodeGlobal, typed]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at outputWf ⊢
    rw [value] at outputWf ⊢
    apply eval_read _ _ _ _ storeWf frameWf inputWf outputWf
    have fetched : fun_global ⟨sourceStore, ⟨[], sourceInstance⟩⟩ (.mk_uN index.val) = decodeGlobal global := by
      exact globals index address global rfl lookup found
    simpa only [Module.Constants.instruction, admininstr_instr, fetched] using
      (Step_read.global_get ⟨sourceStore, ⟨[], sourceInstance⟩⟩ (.mk_uN index.val)
        (Itasca.Spec.wf_config_make storeWf frameWf (by simpa [Forall, Module.Constants.instruction, admininstr_instr] using Itasca.Spec.wf_admininstr_instr inputWf)))

end Itasca.Store

end

/-! ## InitializerSourceContext -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std Itasca

/-- The source initial frame reads the same imported globals and function
addresses as the staged runtime instance. Defined globals are not in the
constant-expression typing context. -/
structure InitializerSourceContext {M : Type} (sourceStore : _root_.store)
    (sourceInstance : moduleinst) (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) : Prop where
  functions : sourceInstance.FUNCS = inst.funcs.val.map (fun address => address.index.val)
  globals : ∀ (index : U32) address global,
    index.val < inst.module.module.env.global_types.val.length →
    index.val < inst.module.module.env.num_imported_globals.val →
    inst.globals.val[index.val]? = some address →
    store.globals.val[address.index.val]? = some global →
    fun_global ⟨sourceStore, ⟨[], sourceInstance⟩⟩ (.mk_uN index.val) = decodeGlobal global

theorem InitializerSourceContext.expression {M : Type} {sourceStore sourceInstance}
    {store : runtime.store.Store M} {inst expr ty words}
    (context : InitializerSourceContext sourceStore sourceInstance store inst)
    (valid : Module.Constants.Valid inst.module.module.env expr ty)
    (resolved : Interp.InitializerResolution store inst expr ty words)
    (storeWf : wf_store sourceStore) (frameWf : wf_frame ⟨[], sourceInstance⟩) :
    Eval_expr ⟨sourceStore, ⟨[], sourceInstance⟩⟩ (Module.Constants.expression expr)
      ⟨sourceStore, ⟨[], sourceInstance⟩⟩
      [decodeWords ty ((words[0]?).getD 0#u64) ((words[1]?).getD 0#u64)] := by
  apply initializer_resolution_source_in_state store inst expr ty words resolved
    sourceStore sourceInstance context.functions ?_ storeWf frameWf
  intro index address global equal mapped found
  subst expr
  cases valid with
  | globalGet _ _ typedBound _ imported _ => exact context.globals index address global typedBound imported mapped found

/-- Earlier source lookups are unchanged when only defined globals append. -/
theorem InitializerSourceContext.extend {M : Type} {sourceStore sourceInstance}
    {before after : runtime.store.Store M} {old next : runtime.store.ModuleInst}
    (context : InitializerSourceContext sourceStore sourceInstance before old)
    (imports : InitializerImports before old)
    (source : next.module = old.module) (functions : next.funcs = old.funcs)
    (globalMap : next.globals.val.take old.globals.length = old.globals.val)
    (globals : after.globals.val.take before.globals.length = before.globals.val) :
    InitializerSourceContext sourceStore sourceInstance after next := by
  refine ⟨by simpa [functions] using context.functions, ?_⟩
  intro index address global typedBound imported mapped found
  rw [source] at typedBound imported
  obtain ⟨oldAddress, oldGlobal, oldMapped, oldFound, _⟩ := imports.globals index
    old.module.module.env.global_types.val[index.val] (List.getElem?_eq_getElem typedBound) imported
  have mapBound := (List.getElem?_eq_some_iff.mp oldMapped).1
  have mapRetained := oldMapped
  rw [← globalMap, List.getElem?_take, if_pos mapBound] at mapRetained
  have sameAddress : oldAddress = address := Option.some.inj (mapRetained.symm.trans mapped)
  subst oldAddress
  have globalBound := (List.getElem?_eq_some_iff.mp oldFound).1
  have globalRetained := oldFound
  rw [← globals, List.getElem?_take, if_pos globalBound] at globalRetained
  have sameGlobal : oldGlobal = global := Option.some.inj (globalRetained.symm.trans found)
  subst oldGlobal
  exact context.globals index address global typedBound imported oldMapped oldFound

/-- Preparation has not changed global contents; its imported address map is
exactly the initial source frame's global namespace. -/
theorem InitializerSourceContext.of_maps {M : Type} (view : M → Slice U8)
    (code : CodeInterpretation) (before store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (sourceInstance : moduleinst)
    (functions : sourceInstance.FUNCS = inst.funcs.val.map (fun address => address.index.val))
    (addresses : sourceInstance.GLOBALS = inst.globals.val.map (fun address => address.index.val))
    (globals : store.globals = before.globals) :
    InitializerSourceContext (decodeStore view code before) sourceInstance store inst := by
  refine ⟨functions, ?_⟩
  intro index address global _ _ mapped found
  rw [globals] at found
  simp [fun_global, decodeStore, addresses, proj_uN_0,
    List.getElem!_eq_getElem?_getD, List.getElem?_map, mapped, found]
end Itasca.Store

end

/-! ## Data -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

@[step] theorem copy_bytes_loop (source : Slice U8) (bytes : alloc.vec.Vec U8)
    (i : Usize) (hi : i.val ≤ source.length) (hprefix : bytes.val = source.val.take i.val) :
    runtime.store.copy_bytes_loop source bytes i ⦃ after => after.val = source.val ⦄ := by
  unfold runtime.store.copy_bytes_loop
  apply loop.spec_decr_nat (fun pair => source.length - pair.2.val)
    (fun pair => pair.2.val ≤ source.length ∧ pair.1.val = source.val.take pair.2.val)
  · intro pair hinv
    rcases pair with ⟨bytes, i⟩
    rcases hinv with ⟨hi, hbytes⟩
    unfold runtime.store.copy_bytes_loop.body
    dsimp only at hi hbytes ⊢
    split
    · rename_i hmore
      have hib : i.val < source.length := by scalar_tac
      have hlen : bytes.length = i.val := by simp [hbytes, Nat.min_eq_left hi]
      have hmax : bytes.length < Usize.max := by scalar_tac
      step as ⟨value, hvalue⟩
      step as ⟨after, hafter⟩
      step as ⟨next, hnext⟩
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [hafter, hbytes, hnext, List.take_succ_eq_append_getElem hib, hvalue]
    · rename_i hstop
      have heq : i.val = source.length := by scalar_tac
      simpa [heq] using hbytes
  · exact ⟨hi, hprefix⟩

@[step] theorem copy_bytes_spec {A : Type} (allocator : runtime.platform.Alloc A)
    (ha : Platform.AllocCorrect allocator) (source : Slice U8) :
    runtime.store.copy_bytes allocator source ⦃ answer =>
      answer = .Err (.Exhausted .Allocation) ∨ ∃ bytes, answer = .Ok bytes ∧ bytes.val = source.val ⦄ := by
  unfold runtime.store.copy_bytes
  dsimp only
  obtain ⟨reserved, hr⟩ := reserve_wrapper_eq allocator ha (alloc.vec.Vec.new U8) (Slice.len source)
  rw [hr]
  cases reserved
  · simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · simp [core.result.Result.Insts.CoreOpsTry.branch]
    step with copy_bytes_loop source (alloc.vec.Vec.new U8) 0#usize (by scalar_tac) (by simp) as ⟨bytes, hbytes⟩
    simp [hbytes]

/-- A data segment is copied byte for byte and receives its current store index.
Failures do not change the store; success changes only that data vector and the
selected provisional instance's data-address map. -/
theorem add_instance_data_effect {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (ha : Platform.AllocCorrect allocator)
    (s : runtime.store.Store M) (instanceIndex i : Usize)
    (hinstance : instanceIndex.val < s.instances.length)
    (hi : i.val < (s.instances.val[instanceIndex.val]).module.module.tail.data.length)
    (hroom : s.datas.length < Usize.max)
    (hmaproom : (s.instances.val[instanceIndex.val]).datas.length < Usize.max) :
    runtime.store.instantiate.Store.add_instance_data ops allocator s instanceIndex i ⦃ result =>
      (∃ error, result = (.Err error, s)) ∨
      ∃ bytes : alloc.vec.Vec U8, ∃ datas : alloc.vec.Vec runtime.store.DataInst,
      ∃ addresses : alloc.vec.Vec Usize,
        bytes.val = (s.instances.val[instanceIndex.val]).module.module.tail.data.val[i.val].init.val ∧
        datas.val = s.datas.val ++ [⟨bytes⟩] ∧
        addresses.val = (s.instances.val[instanceIndex.val]).datas.val ++ [alloc.vec.Vec.len s.datas] ∧
        result = (.Ok (), {s with datas := datas, instances := s.instances.set instanceIndex {(s.instances.val[instanceIndex.val]) with datas := addresses}}) ⦄ := by
  unfold runtime.store.instantiate.Store.add_instance_data
  step as ⟨inst, hinst⟩
  simp only [runtime.compiler.ExecutableModule.tail.eq, bind_ok]
  have hd : i.val < inst.module.module.tail.data.length := by simpa [hinst] using hi
  step as ⟨data, hdata⟩
  step with copy_bytes_spec allocator ha data.init.deref as ⟨copied, hcopied⟩
  rcases hcopied with herr | ⟨bytes, hok, hbytes⟩
  · simp [herr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · rw [hok]
    simp [core.result.Result.Insts.CoreOpsTry.branch]
    obtain ⟨reserved, hr⟩ := reserve_wrapper_eq allocator ha s.datas 1#usize
    rw [hr]
    cases reserved
    · simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    · simp [core.result.Result.Insts.CoreOpsTry.branch]
      step as ⟨datas, hdatas⟩
      step as ⟨inst', back, hinst', hback⟩
      have hm : inst'.datas.length < Usize.max := by simpa [hinst'] using hmaproom
      step as ⟨addresses, haddresses⟩
      right
      refine ⟨bytes, ?_, datas, hdatas, addresses, ?_, ?_⟩
      · simpa [hdata, hinst, alloc.vec.Vec.deref] using hbytes
      · simpa [hinst'] using haddresses
      · simp [hback, hinst']

end Itasca.Store

end

end

/-! ## BulkInitialization -/

section

open Itasca.Representation

/-!
# Bulk Initialization

Bulk memory and table initialization connect segment bounds to concrete store effects.
-/

/-! ## BulkTableAt -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std
theorem bulk_table_init_at {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (operand entry element tableId : U32) (address : Usize) (tableAddress : runtime.TableAddr)
    (table : runtime.store.TableInst) (segment : runtime.store.ElemInst)
    (destination source count : U64)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some code)
    (descriptor : code.indirect.val[entry.val]? = some (element, tableId))
    (mapped : inst.elems.val[element.val]? = some address)
    (resolved : store.elems.val[address.val]? = some segment)
    (tableMapped : inst.tables.val[tableId.val]? = some tableAddress)
    (target : store.tables.val[tableAddress.index.val]? = some table)
    (destinationSlot : slots.val[base.val+operand.val]? = some destination)
    (sourceSlot : slots.val[base.val+operand.val+1]? = some source)
    (countSlot : slots.val[base.val+operand.val+2]? = some count) :
    runtime.interp.bulk.execute memory store instIndex function base slots (.TableInit operand entry)
      ⦃ out => TableInitializationEffect store tableAddress.index table segment
        (bulkWord destination) (bulkWord source) (bulkWord count) out ⦄ := by
  simp only [runtime.interp.bulk.execute]
  step with Interp.vec_index_given store.instances instIndex inst found as ⟨actual, actualEq⟩
  subst actual
  step with Interp.vec_index_given inst.module.functions function code functionFound as ⟨actual, actualEq⟩
  subst actual
  simp only [lift, bind_ok]
  step with Interp.vec_index_given code.indirect (UScalar.cast .Usize entry) (element, tableId)
    (by simpa using descriptor) as ⟨a, b, aEq, bEq⟩
  subst a b
  have bound := (List.getElem?_eq_some_iff.mp countSlot).1
  step as ⟨position,positionEq⟩
  have pos : position.val = base.val+operand.val := by simpa only [U32.cast_Usize_val_eq] using positionEq
  rw [Compiler.initializer_slice_index slots position destination (by simpa only [pos] using destinationSlot)]
  simp only [bind_ok,lift]
  step as ⟨position1,position1Eq⟩
  step as ⟨position2,position2Eq⟩
  have pos2 : position2.val = base.val+operand.val+1 := by simpa only [position1Eq,U32.cast_Usize_val_eq] using position2Eq
  rw [Compiler.initializer_slice_index slots position2 source (by simpa only [pos2] using sourceSlot)]
  simp only [bind_ok,lift]
  step as ⟨position3,position3Eq⟩
  step as ⟨position4,position4Eq⟩
  have pos4 : position4.val = base.val+operand.val+2 := by simpa only [position3Eq,U32.cast_Usize_val_eq] using position4Eq
  rw [Compiler.initializer_slice_index slots position4 count (by simpa only [pos4] using countSlot)]
  simp only [bind_ok,lift]
  step with Interp.vec_index_given inst.tables (UScalar.cast .Usize tableId) tableAddress
    (by simpa using tableMapped) as ⟨actual, actualEq⟩
  subst actual
  step with Interp.vec_index_given store.tables tableAddress.index table target as ⟨actual, actualEq⟩
  subst actual
  step with Interp.range_effect (bulkWord destination) (bulkWord count) (alloc.vec.Vec.len table.elements)
    .TableOutOfBounds as ⟨result, rangeEffect⟩
  by_cases fitsTarget : (bulkWord destination).val + (bulkWord count).val ≤ table.elements.length
  · change (if (bulkWord destination).val + (bulkWord count).val ≤ table.elements.length then _ else _) at rangeEffect
    rw [if_pos fitsTarget] at rangeEffect
    obtain ⟨dst, rfl, dstStart, dstEnd⟩ := rangeEffect
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with Interp.vec_index_given inst.elems (UScalar.cast .Usize element) address
      (by simpa using mapped) as ⟨actual, actualEq⟩
    subst actual
    step with Interp.vec_index_given store.elems address segment resolved as ⟨actual, actualEq⟩
    subst actual
    step with Interp.range_effect (bulkWord source) (bulkWord count) (alloc.vec.Vec.len segment.refs)
      .TableOutOfBounds as ⟨result, rangeEffect⟩
    by_cases fitsSource : (bulkWord source).val + (bulkWord count).val ≤ segment.refs.length
    · change (if (bulkWord source).val + (bulkWord count).val ≤ segment.refs.length then _ else _) at rangeEffect
      rw [if_pos fitsSource] at rangeEffect
      obtain ⟨src, rfl, srcStart, srcEnd⟩ := rangeEffect
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with table_init_loop store.tables store.instances store.elems instIndex element (bulkWord count)
        tableAddress.index dst src inst address segment table found mapped resolved target
        (by simpa only [srcStart] using fitsSource) (by simpa only [dstStart] using fitsTarget)
        as ⟨tables, words, tablesEq, valuesEq⟩
      simp only [TableInitializationEffect, fitsSource, fitsTarget, and_self, ↓reduceIte]
      exact ⟨words, by rw [tablesEq], by simpa only [srcStart, dstStart] using valuesEq⟩
    · change (if (bulkWord source).val + (bulkWord count).val ≤ segment.refs.length then _ else _) at rangeEffect
      rw [if_neg fitsSource] at rangeEffect
      rw [rangeEffect]
      simp_all [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        TableInitializationEffect]
  · change (if (bulkWord destination).val + (bulkWord count).val ≤ table.elements.length then _ else _) at rangeEffect
    rw [if_neg fitsTarget] at rangeEffect
    rw [rangeEffect]
    simp_all [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      TableInitializationEffect]

end Itasca.Store

end

/-! ## BulkMemoryAt -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std
theorem bulk_memory_init_at {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws ops view)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (inst : runtime.store.ModuleInst) (operand data : U32) (address : Usize) (memoryAddress : runtime.MemoryAddr)
    (memory : runtime.store.MemInst M) (segment : runtime.store.DataInst)
    (destination source count : U64)
    (found : store.instances.val[instIndex.val]? = some inst)
    (mapped : inst.datas.val[data.val]? = some address)
    (resolved : store.datas.val[address.val]? = some segment)
    (memoryMapped : inst.memories.val[0]? = some memoryAddress)
    (target : store.memories.val[memoryAddress.index.val]? = some memory)
    (destinationSlot : slots.val[base.val+operand.val]? = some destination)
    (sourceSlot : slots.val[base.val+operand.val+1]? = some source)
    (countSlot : slots.val[base.val+operand.val+2]? = some count) :
    runtime.interp.bulk.execute ops store instIndex function base slots (.MemoryInit operand data)
      ⦃ out => MemoryInitializationEffect view store memoryAddress.index memory segment
        (bulkWord destination) (bulkWord source) (bulkWord count) out ⦄ := by
  have bound := (List.getElem?_eq_some_iff.mp countSlot).1
  simp only [runtime.interp.bulk.execute,lift,bind_ok]
  step as ⟨position,positionEq⟩
  have pos : position.val = base.val+operand.val := by simpa only [U32.cast_Usize_val_eq] using positionEq
  rw [Compiler.initializer_slice_index slots position destination (by simpa only [pos] using destinationSlot)]
  simp only [bind_ok,lift]
  step as ⟨position1,position1Eq⟩
  step as ⟨position2,position2Eq⟩
  have pos2 : position2.val = base.val+operand.val+1 := by simpa only [position1Eq,U32.cast_Usize_val_eq] using position2Eq
  rw [Compiler.initializer_slice_index slots position2 source (by simpa only [pos2] using sourceSlot)]
  simp only [bind_ok,lift]
  step as ⟨position3,position3Eq⟩
  step as ⟨position4,position4Eq⟩
  have pos4 : position4.val = base.val+operand.val+2 := by simpa only [position3Eq,U32.cast_Usize_val_eq] using position4Eq
  rw [Compiler.initializer_slice_index slots position4 count (by simpa only [pos4] using countSlot)]
  simp only [bind_ok,lift]
  step with Interp.vec_index_given store.instances instIndex inst found as ⟨actual, actualEq⟩
  subst actual
  step with Interp.vec_index_given inst.memories 0#usize memoryAddress memoryMapped as ⟨actual, actualEq⟩
  subst actual
  step with Interp.vec_index_given store.memories memoryAddress.index memory target as ⟨actual, actualEq⟩
  subst actual
  rw [laws.read, bind_ok]
  step with Interp.range_effect (bulkWord destination) (bulkWord count) (Slice.len (view memory.buf))
    .MemoryOutOfBounds as ⟨result, rangeEffect⟩
  by_cases fitsTarget : (bulkWord destination).val + (bulkWord count).val ≤ (view memory.buf).length
  · change (if (bulkWord destination).val + (bulkWord count).val ≤ (view memory.buf).length then _ else _) at rangeEffect
    rw [if_pos fitsTarget] at rangeEffect
    obtain ⟨dst, rfl, dstStart, dstEnd⟩ := rangeEffect
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with Interp.vec_index_given inst.datas (UScalar.cast .Usize data) address
      (by simpa using mapped) as ⟨actual, actualEq⟩
    subst actual
    step with Interp.vec_index_given store.datas address segment resolved as ⟨actual, actualEq⟩
    subst actual
    step with Interp.range_effect (bulkWord source) (bulkWord count) (alloc.vec.Vec.len segment.bytes)
      .MemoryOutOfBounds as ⟨result, rangeEffect⟩
    by_cases fitsSource : (bulkWord source).val + (bulkWord count).val ≤ segment.bytes.length
    · change (if (bulkWord source).val + (bulkWord count).val ≤ segment.bytes.length then _ else _) at rangeEffect
      rw [if_pos fitsSource] at rangeEffect
      obtain ⟨src, rfl, srcStart, srcEnd⟩ := rangeEffect
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have memoryBound : memoryAddress.index.val < store.memories.length :=
        (List.getElem?_eq_some_iff.mp target).1
      have memoryRead : store.memories.val[memoryAddress.index.val] = memory :=
        (List.getElem?_eq_some_iff.mp target).2
      step as ⟨actualMemory, memoryBack, actualMemoryEq, memoryBackEq⟩
      have sameMemory : actualMemory = memory := actualMemoryEq.trans memoryRead
      rw [sameMemory]
      obtain ⟨back, write, viewBack⟩ := laws.write memory.buf
      rw [write, bind_ok]
      have dstOrder : dst.start ≤ dst.end := by scalar_tac
      have dstBound : dst.end.val ≤ (view memory.buf).length := by omega
      have srcOrder : src.start ≤ src.end := by scalar_tac
      have srcBound : src.end.val ≤ segment.bytes.length := by omega
      step as ⟨targetSlice, targetBack, targetValues, targetLength, targetBackEq⟩
      step as ⟨sourceSlice, sourceValues, sourceLength⟩
      have sameLength : targetSlice.length = sourceSlice.length := by omega
      step as ⟨copied, copiedEq⟩
      subst copied
      simp only [MemoryInitializationEffect, fitsSource, fitsTarget, and_self, ↓reduceIte]
      refine ⟨back (targetBack sourceSlice), ?_, ?_⟩
      · simp only [memoryBackEq]
      · rw [targetBackEq, viewBack _ (by simp)]
        rw [Slice.setSlice!_val, sourceValues, dstStart, srcStart, srcEnd]
    · change (if (bulkWord source).val + (bulkWord count).val ≤ segment.bytes.length then _ else _) at rangeEffect
      rw [if_neg fitsSource] at rangeEffect
      rw [rangeEffect]
      simp_all [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        MemoryInitializationEffect]
  · change (if (bulkWord destination).val + (bulkWord count).val ≤ (view memory.buf).length then _ else _) at rangeEffect
    rw [if_neg fitsTarget] at rangeEffect
    rw [rangeEffect]
    simp_all [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      MemoryInitializationEffect]

end Itasca.Store

end

end

end
