import Itasca.Runtime.Compiler.Local.Initializer.ModuleMappings
import Itasca.Runtime.Store.Initialization.SegmentOperations
import Itasca.Module.Elab.SegmentTyping
import ItascaRust.Funs
import Itasca.Runtime.Store.Api.ObjectStaging

/-!
Proofs for Runtime / Store / Initialization.

This module collects InitializerCertificates, DataEffects.
Each section documents its contracts and consumers.
-/

/-! ## InitializerCertificates -/

section

/-! Compiler map certificates and canonical validator constant typing discharge
the structural initializer premises of the actual staged store operations. -/
namespace Itasca.Store
open Aeneas Aeneas.Std

private theorem related_lookup {T U : Type} {relation : T → U → Prop}
    {before : List T} {after : List U} (related : List.Forall₂ relation before after)
    {index : Nat} {value : T} (found : before[index]? = some value) :
    ∃ result, after[index]? = some result ∧ relation value result := by
  induction related generalizing index with
  | nil => simp at found
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst value
      exact ⟨_, rfl, head⟩
    | succ index =>
      exact ih (by simpa only [List.getElem?_cons_succ] using found)

theorem global_initializer_certificate {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (index : Usize) (global : Itasca.metadata.Global)
    (compiled : Compiler.InitializerMappings inst.module)
    (found : inst.module.module.env.globals.val[index.val]? = some global)
    (valid : Itasca.Module.Constants.Valid inst.module.module.env global.init global.gtype.valtype)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst) :
    ∃ function code words,
      inst.module.global_initializers.val[index.val]? = some function ∧
      inst.module.functions.val[function.val]? = some code ∧
      Compiler.InitializerCode code global.init global.gtype.valtype ∧
      Interp.InitializerResolution store inst global.init global.gtype.valtype words := by
  obtain ⟨function, mapped, code, read, certificate⟩ := related_lookup compiled.globals found
  obtain ⟨words, resolved⟩ := initializer_resolves store inst global.init global.gtype.valtype valid bindings imports
  exact ⟨function, code, words, mapped, read, certificate, resolved⟩

theorem element_initializer_certificates {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (index : Usize) (segment : Itasca.metadata.Element)
    (compiled : Compiler.InitializerMappings inst.module)
    (found : inst.module.module.env.elements.val[index.val]? = some segment)
    (valid : Itasca.Module.Segments.elementValid inst.module.module.env segment)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst) :
    ElementInitializers store inst index segment := by
  obtain ⟨indices, mapped, entries⟩ := related_lookup compiled.elementValues found
  refine ⟨indices, mapped, ?_⟩
  intro j bound
  let expr := segment.init.val[j.val]
  have read : segment.init.val[j.val]? = some expr := List.getElem?_eq_getElem bound
  obtain ⟨function, indexed, code, codeFound, certificate⟩ := related_lookup entries read
  have typed := valid.2 expr (List.mem_of_getElem? read)
  obtain ⟨words, resolved⟩ := initializer_resolves store inst expr _ typed bindings imports
  have sameType : Itasca.Module.Constants.referenceValueType segment.elem = elementValueType segment.elem := by
    cases segment.elem <;> rfl
  exact ⟨expr, function, code, words, read, indexed, codeFound,
    sameType ▸ certificate, sameType ▸ resolved⟩

/-- Issued table and memory maps cover the validated module index spaces.
These are structural link/staging facts, with no execution postcondition. -/
structure InitializerSegmentBindings {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) : Prop where
  tableCount : inst.module.module.env.table_types.val.length ≤ inst.tables.val.length
  memoryCount : inst.module.module.env.mem_types.val.length ≤ inst.memories.val.length
  tables : ∀ addr ∈ inst.tables.val, addr.index.val < store.tables.val.length
  memories : ∀ addr ∈ inst.memories.val, addr.index.val < store.memories.val.length

end Itasca.Store

end

/-! ## DataEffects -/

section

open Itasca.Representation

/-!
Data-segment allocation, result classification and decoded payload. Cross-segment metadata preservation stays in its separately consumed adapter.
-/

/-! ## Data Effects -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

inductive DataStageEffect {M : Type} (store : runtime.store.Store M)
    (instIndex : Usize) (inst : runtime.store.ModuleInst) : runtime.store.Store M → Prop where
  | unchanged : DataStageEffect store instIndex inst store
  | appended (datas : alloc.vec.Vec runtime.store.DataInst)
      (addresses : alloc.vec.Vec Usize) (data : runtime.store.DataInst)
      (dataValues : datas.val = store.datas.val ++ [data])
      (addressValues : addresses.val = inst.datas.val ++ [store.datas.len]) :
      DataStageEffect store instIndex inst
        { store with datas := datas, instances := store.instances.set instIndex { inst with datas := addresses } }

theorem add_instance_data_stage_effect {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (instIndex index : Usize) (inst : runtime.store.ModuleInst)
    (found : store.instances.val[instIndex.val]? = some inst)
    (bound : index.val < inst.module.module.tail.data.val.length)
    (room : store.datas.length < Usize.max) (mapRoom : inst.datas.length < Usize.max) :
    runtime.store.instantiate.Store.add_instance_data memory allocator store instIndex index
      ⦃ out => DataStageEffect store instIndex inst out.2 ⦄ := by
  have instanceBound : instIndex.val < store.instances.length := (List.getElem?_eq_some_iff.mp found).1
  have instanceRead : store.instances.val[instIndex.val] = inst :=
    Option.some.inj ((List.getElem?_eq_getElem instanceBound).symm.trans found)
  apply WP.spec_mono (add_instance_data_effect memory allocator law store instIndex index instanceBound
    (by simpa only [instanceRead] using bound) room (by simpa only [instanceRead] using mapRoom))
  intro out effect
  rcases effect with ⟨error, rfl⟩ | ⟨bytes, datas, addresses, copied, appended, mapped, rfl⟩
  · exact .unchanged
  · simpa only [instanceRead] using DataStageEffect.appended (store := store) (instIndex := instIndex)
      (inst := inst) datas addresses ⟨bytes⟩ appended (by simpa only [instanceRead] using mapped)

theorem DataStageEffect.context {M : Type} {store after : runtime.store.Store M}
    {instIndex : Usize} {inst : runtime.store.ModuleInst}
    (effect : DataStageEffect store instIndex inst after)
    (found : store.instances.val[instIndex.val]? = some inst)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst) :
    ∃ next, after.instances.val[instIndex.val]? = some next ∧ next.module = inst.module ∧
      InitializerBindings after next ∧ InitializerImports after next ∧
      InitializerSegmentBindings after next ∧ next.datas.length ≤ inst.datas.length + 1 ∧
      after.datas.length ≤ store.datas.length + 1 := by
  cases effect with
  | unchanged => exact ⟨inst, found, rfl, bindings, imports, segments, by omega, by omega⟩
  | appended datas addresses data dataValues addressValues =>
    have bound : instIndex.val < store.instances.val.length := (List.getElem?_eq_some_iff.mp found).1
    refine ⟨{inst with datas := addresses}, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp [alloc.vec.Vec.set_val_eq, bound]
    · exact ⟨bindings.funcs, bindings.globals⟩
    · exact imports.extend rfl rfl (by simp) (by simp)
    · exact ⟨segments.tableCount, segments.memoryCount, segments.tables, segments.memories⟩
    · simp [addressValues]
    · simp [dataValues]

theorem DataStageEffect.object_count {M : Type} {store after : runtime.store.Store M}
    {instIndex : Usize} {inst : runtime.store.ModuleInst}
    (effect : DataStageEffect store instIndex inst after) : objectCount after = objectCount store := by
  cases effect <;> rfl

theorem DataStageEffect.staged {M : Type} {before store after : runtime.store.Store M}
    {instIndex : Usize} {inst : runtime.store.ModuleInst}
    (effect : DataStageEffect store instIndex inst after)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ instIndex.val) :
    StagedPrefix before after := by
  cases effect with
  | unchanged => exact staged
  | appended datas addresses data dataValues addressValues =>
    have appended : StagedPrefix store {store with datas := datas} := by
      constructor <;> simp [dataValues]
    exact (staged.trans appended).set_fresh_instance instIndex {inst with datas := addresses} fresh

end Itasca.Store

end

/-! ## Data Result Effect -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

inductive DataResultEffect {M : Type} (store : runtime.store.Store M)
    (instIndex : Usize) (inst : runtime.store.ModuleInst) : core.result.Result Unit runtime.ExecError → runtime.store.Store M → Prop where
  | failed (error : runtime.ExecError) : DataResultEffect store instIndex inst (.Err error) store
  | appended (datas : alloc.vec.Vec runtime.store.DataInst)
      (addresses : alloc.vec.Vec Usize) (data : runtime.store.DataInst)
      (dataValues : datas.val = store.datas.val ++ [data])
      (addressValues : addresses.val = inst.datas.val ++ [store.datas.len]) :
      DataResultEffect store instIndex inst (.Ok ())
        { store with datas := datas, instances := store.instances.set instIndex { inst with datas := addresses } }

theorem add_instance_data_result_effect {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (instIndex index : Usize) (inst : runtime.store.ModuleInst)
    (found : store.instances.val[instIndex.val]? = some inst)
    (bound : index.val < inst.module.module.tail.data.val.length)
    (room : store.datas.length < Usize.max) (mapRoom : inst.datas.length < Usize.max) :
    runtime.store.instantiate.Store.add_instance_data memory allocator store instIndex index
      ⦃ out => DataResultEffect store instIndex inst out.1 out.2 ⦄ := by
  have instanceBound : instIndex.val < store.instances.length := (List.getElem?_eq_some_iff.mp found).1
  have instanceRead : store.instances.val[instIndex.val] = inst :=
    Option.some.inj ((List.getElem?_eq_getElem instanceBound).symm.trans found)
  apply WP.spec_mono (add_instance_data_effect memory allocator law store instIndex index instanceBound
    (by simpa only [instanceRead] using bound) room (by simpa only [instanceRead] using mapRoom))
  intro out effect
  rcases effect with ⟨error, rfl⟩ | ⟨bytes, datas, addresses, copied, appended, mapped, rfl⟩
  · exact .failed error
  · simpa only [instanceRead] using DataResultEffect.appended (store := store) (instIndex := instIndex)
      (inst := inst) datas addresses ⟨bytes⟩ appended (by simpa only [instanceRead] using mapped)

theorem DataResultEffect.effect {M : Type} {store after : runtime.store.Store M}
    {instIndex inst status} (effect : DataResultEffect store instIndex inst status after) :
    DataStageEffect store instIndex inst after := by
  cases effect with
  | failed error => exact .unchanged
  | appended datas addresses data stored mapped => exact .appended datas addresses data stored mapped

theorem DataResultEffect.count {M : Type} {store after : runtime.store.Store M}
    {instIndex inst status} (effect : DataResultEffect store instIndex inst status after)
    (bound : instIndex.val < store.instances.length) {next : runtime.store.ModuleInst}
    (found : after.instances.val[instIndex.val]? = some next) (success : status = .Ok ()) :
    next.datas.length = inst.datas.length + 1 := by
  cases effect with
  | failed error => simp at success
  | appended datas addresses data stored mapped =>
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at found
    subst next
    simp [mapped]

end Itasca.Store

end

/-! ## Data Payload -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

def sourceDataPayload (segment : Itasca.metadata.Data) : datainst :=
  ⟨segment.init.val.map (fun byte => .mk_byte byte.val)⟩

theorem add_instance_data_payload {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (instIndex index : Usize) (inst : runtime.store.ModuleInst)
    (found : store.instances.val[instIndex.val]? = some inst)
    (bound : index.val < inst.module.module.tail.data.val.length)
    (room : store.datas.length < Usize.max) (mapRoom : inst.datas.length < Usize.max) :
    runtime.store.instantiate.Store.add_instance_data memory allocator store instIndex index
      ⦃ out => DataResultEffect store instIndex inst out.1 out.2 ∧
        (out.1 = .Ok () → out.2.datas.val.map decodeData =
          store.datas.val.map decodeData ++ [sourceDataPayload inst.module.module.tail.data.val[index.val]]) ⦄ := by
  have instanceBound : instIndex.val < store.instances.length := (List.getElem?_eq_some_iff.mp found).1
  have instanceRead : store.instances.val[instIndex.val] = inst :=
    Option.some.inj ((List.getElem?_eq_getElem instanceBound).symm.trans found)
  apply WP.spec_mono (add_instance_data_effect memory allocator law store instIndex index instanceBound
    (by simpa only [instanceRead] using bound) room (by simpa only [instanceRead] using mapRoom))
  intro out effect
  rcases effect with ⟨error, rfl⟩ | ⟨bytes, datas, addresses, copied, appended, mapped, rfl⟩
  · exact ⟨.failed error, by simp⟩
  · constructor
    · simpa only [instanceRead] using DataResultEffect.appended (store := store) (instIndex := instIndex)
        (inst := inst) datas addresses ⟨bytes⟩ appended (by simpa only [instanceRead] using mapped)
    · intro _
      simp only [List.map_append, List.map_cons, List.map_nil, appended, decodeData,
        copied, instanceRead, sourceDataPayload, decodeBytes]
end Itasca.Store

end

end
