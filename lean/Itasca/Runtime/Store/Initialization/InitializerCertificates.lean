import Itasca.Runtime.Code.Local.Initializer.InitializerComplete
import Itasca.Runtime.Store.Initialization.InitializerResolve
import Itasca.Runtime.Store.Initialization.ElementLoop
import Itasca.Runtime.Store.Initialization.PrecheckLoop
import Itasca.Module.Elab.SegmentSyntax

/-! Compiler map certificates and canonical validator constant typing discharge
the structural initializer premises of the actual staged store operations. -/
namespace Itasca.Runtime.Store
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
    (inst : runtime.store.ModuleInst) (index : Usize) (global : Itasca.module.Global)
    (compiled : Code.InitializerMappings inst.module)
    (found : inst.module.module.env.globals.val[index.val]? = some global)
    (valid : Itasca.ModuleConstants.Valid inst.module.module.env global.init global.gtype.valtype)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst) :
    ∃ function code words,
      inst.module.global_initializers.val[index.val]? = some function ∧
      inst.module.functions.val[function.val]? = some code ∧
      Code.InitializerCode code global.init global.gtype.valtype ∧
      Interp.InitializerResolution store inst global.init global.gtype.valtype words := by
  obtain ⟨function, mapped, code, read, certificate⟩ := related_lookup compiled.globals found
  obtain ⟨words, resolved⟩ := initializer_resolves store inst global.init global.gtype.valtype valid bindings imports
  exact ⟨function, code, words, mapped, read, certificate, resolved⟩

theorem element_initializer_certificates {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (index : Usize) (segment : Itasca.module.Element)
    (compiled : Code.InitializerMappings inst.module)
    (found : inst.module.module.env.elements.val[index.val]? = some segment)
    (valid : Itasca.ModuleSegments.elementValid inst.module.module.env segment)
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
  have sameType : Itasca.ModuleConstants.referenceValueType segment.elem = elementValueType segment.elem := by
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

theorem element_precheck_certificate {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (index : Usize) (segment : Itasca.module.Element)
    (compiled : Code.InitializerMappings inst.module)
    (found : inst.module.module.env.elements.val[index.val]? = some segment)
    (valid : Itasca.ModuleSegments.elementValid inst.module.module.env segment)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst) :
    ElementPrecheckReady store inst index segment := by
  cases mode : segment.mode with
  | Passive => simp [ElementPrecheckReady, mode]
  | Declarative => simp [ElementPrecheckReady, mode]
  | Active tableIndex expr =>
    simp only [ElementPrecheckReady, mode]
    obtain ⟨offset, mapped, certificate⟩ := related_lookup compiled.elementOffsets found
    simp only [Code.OffsetInitializer, Code.sourceElementOffset, mode] at certificate
    cases offset with
    | none => contradiction
    | some function =>
      obtain ⟨code, codeFound, codeCert⟩ := certificate
      obtain ⟨tableBound, tableType, typed⟩ := (show ∃ bound : tableIndex.val < inst.module.module.env.table_types.val.length,
        inst.module.module.env.table_types.val[tableIndex.val].elem = segment.elem ∧
        Itasca.ModuleConstants.Valid inst.module.module.env expr .I32 from by simpa [mode] using valid.1)
      obtain ⟨words, resolved⟩ := initializer_resolves store inst expr .I32 typed bindings imports
      have mapBound : tableIndex.val < inst.tables.val.length := by have := segments.tableCount; omega
      let addr := inst.tables.val[tableIndex.val]
      have addrFound : inst.tables.val[tableIndex.val]? = some addr := List.getElem?_eq_getElem mapBound
      have issued := segments.tables addr (List.mem_of_getElem? addrFound)
      let table := store.tables.val[addr.index.val]
      refine ⟨function, code, words, addr, table, mapped, codeFound, codeCert, resolved, addrFound, ?_⟩
      exact List.getElem?_eq_getElem issued

theorem data_precheck_certificate {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (index : Usize) (segment : Itasca.module.Data)
    (compiled : Code.InitializerMappings inst.module)
    (found : inst.module.module.tail.data.val[index.val]? = some segment)
    (valid : Itasca.ModuleData.Valid inst.module.module.env segment)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst) :
    DataPrecheckReady store inst index segment := by
  cases mode : segment.mode with
  | Passive => simp [DataPrecheckReady, mode]
  | Active memoryIndex expr =>
    simp only [DataPrecheckReady, mode]
    obtain ⟨offset, mapped, certificate⟩ := related_lookup compiled.dataOffsets found
    simp only [Code.OffsetInitializer, Code.sourceDataOffset, mode] at certificate
    cases offset with
    | none => contradiction
    | some function =>
      obtain ⟨code, codeFound, codeCert⟩ := certificate
      obtain ⟨memoryBound, typed⟩ := (show memoryIndex.val < inst.module.module.env.mem_types.val.length ∧
        Itasca.ModuleConstants.Valid inst.module.module.env expr .I32 from by simpa [Itasca.ModuleData.Valid, mode] using valid)
      obtain ⟨words, resolved⟩ := initializer_resolves store inst expr .I32 typed bindings imports
      have mapBound : memoryIndex.val < inst.memories.val.length := by have := segments.memoryCount; omega
      let addr := inst.memories.val[memoryIndex.val]
      have addrFound : inst.memories.val[memoryIndex.val]? = some addr := List.getElem?_eq_getElem mapBound
      have issued := segments.memories addr (List.mem_of_getElem? addrFound)
      let memory := store.memories.val[addr.index.val]
      refine ⟨function, code, words, addr, memory, mapped, codeFound, codeCert, resolved, addrFound, ?_⟩
      exact List.getElem?_eq_getElem issued

end Itasca.Runtime.Store
