import Exec.Store.Invariant.BindingMaps
import Exec.Store.Invariant.FunctionSignatures
import Exec.Store.Initialization.SegmentTypes
import Exec.Code.Local.Source.SourceFunctionTyping
namespace Exec.Store
open Aeneas Aeneas.Std Itasca

theorem decodeFuncType_source (ty : types.FuncType) : decodeFuncType ty = EnvTranslation.funcType ty := by
  have same : Interp.sourceType = Translate.valueType := by funext t; cases t <;> rfl
  simp only [decodeFuncType, EnvTranslation.funcType, same]

theorem SegmentTypeBindings.element_map {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} (bindings : SegmentTypeBindings store inst)
    (shape : InstanceShape store inst) :
    ElementTypeMap store inst.module.module.env.elements.val inst.elems.val := by
  obtain ⟨_, _, _, _, _, count, _, _, _, _, _, _, issued, _⟩ := shape
  apply List.forall₂_of_length_eq_of_get (by exact count.symm)
  intro index sourceBound addressBound
  let source := inst.module.module.env.elements.val[index]
  let address := inst.elems.val[index]
  have mapped : inst.elems.val[index]? = some address := List.getElem?_eq_getElem addressBound
  have bound := issued address (List.mem_of_getElem? mapped)
  let element := store.elems.val[address.val]
  have found : store.elems.val[address.val]? = some element := List.getElem?_eq_getElem bound
  refine ⟨element, found, ?_⟩
  exact bindings.elements index source address element (List.getElem?_eq_getElem sourceBound) mapped found

/-- All module namespaces are tied to their issued runtime maps and the exact
canonical source environment. Import subtyping is discharged by the generated
external-address rules. -/
theorem module_bindings_env {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (shape : Shape view store) (sourceSyntax : StoreSyntax code store)
    (instanceShape : InstanceShape store inst) (bounds : SegmentBounds store)
    (types : TypeEntries store inst.module.module.env.types.val inst.types.val)
    (functions : Interp.FunctionTable store inst (inst.module.module.env.func_types.val.map decodeFuncType))
    (globals : GlobalTypeMap store inst.module.module.env.global_types.val inst.globals.val)
    (tables : TableBindings store inst.module.module.env.table_types.val inst.tables.val)
    (memories : MemoryBindings view store inst.module.module.env.mem_types.val inst.memories.val)
    (segments : SegmentTypeBindings store inst) :
    Abs.ModuleBindings (decodeStore view code store) (decodeInstance store inst)
      (ModuleElaboration.moduleContext inst.module.module.env
        (EnvTranslation.elementTypes inst.module.module.env) inst.module.module.tail.data.length) := by
  have decoded : decodeFuncType = EnvTranslation.funcType := funext decodeFuncType_source
  have wellformed := decodeStore_wf view code store shape sourceSyntax
  have elementMap := segments.element_map instanceShape
  obtain ⟨_, _, _, _, _, _, dataCount, _, _, _, _, _, _, dataIssued⟩ := instanceShape
  constructor
  · simpa only [ModuleElaboration.moduleContext, ← decoded, decodeInstance] using (type_entries_decoded types).symm
  · simpa only [ModuleElaboration.moduleContext, Interp.FunctionsMatch, ← decoded] using functions.source view code
  · exact globals.source view code wellformed
  · exact tables.source view code wellformed shape
  · exact memories.source code wellformed shape
  · exact elementMap.source view code wellformed shape bounds
  · have result := data_addresses_typed view code store inst.datas.val wellformed bounds dataIssued
    change List.Forall₂ _ (inst.datas.val.map UScalar.val) (List.replicate inst.module.module.tail.data.length datatype.OK)
    simpa only [dataCount] using result
  · exact ModuleElaboration.moduleContext_wf _ _ _

/-- Source uniqueness identifies this same binding context with the independent
module used by generated function typing. -/
theorem module_bindings_source {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (raw : ModuleBinary.Module)
    (matched : ModuleElaboration.Matches inst.module.module.env inst.module.module.tail raw)
    (shape : Shape view store) (sourceSyntax : StoreSyntax code store)
    (instanceShape : InstanceShape store inst) (bounds : SegmentBounds store)
    (types : TypeEntries store inst.module.module.env.types.val inst.types.val)
    (functions : Interp.FunctionTable store inst (inst.module.module.env.func_types.val.map decodeFuncType))
    (globals : GlobalTypeMap store inst.module.module.env.global_types.val inst.globals.val)
    (tables : TableBindings store inst.module.module.env.table_types.val inst.tables.val)
    (memories : MemoryBindings view store inst.module.module.env.mem_types.val inst.memories.val)
    (segments : SegmentTypeBindings store inst) :
    Abs.ModuleBindings (decodeStore view code store) (decodeInstance store inst) (ModuleElaboration.contextOf raw) := by
  have contextEq : ModuleElaboration.contextOf raw =
      ModuleElaboration.moduleContext inst.module.module.env
        (EnvTranslation.elementTypes inst.module.module.env) inst.module.module.tail.data.length := by
    conv_lhs => rw [matched.1]
    exact ModuleElaboration.contextOf_fromEnv matched.2
  rw [contextEq]
  exact module_bindings_env view code store inst shape sourceSyntax instanceShape bounds types functions globals tables memories segments

end Exec.Store
