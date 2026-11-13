import Itasca.Runtime.Compiler.Local.Initializer.InitializerComplete
import Itasca.Runtime.Store.Initialization.InitializerResolve
import Itasca.Runtime.Store.Initialization.ElementLoop
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
    (inst : runtime.store.ModuleInst) (index : Usize) (global : Itasca.metadata.Global)
    (compiled : Compiler.InitializerMappings inst.module)
    (found : inst.module.module.env.globals.val[index.val]? = some global)
    (valid : Itasca.ModuleConstants.Valid inst.module.module.env global.init global.gtype.valtype)
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

end Itasca.Runtime.Store
