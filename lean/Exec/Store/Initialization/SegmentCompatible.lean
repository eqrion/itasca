import Exec.Store.Initialization.SegmentTypes

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- For an emitted table initialization, source-segment words and destination
slots have the same reference type. Other instructions impose no type equality. -/
def SegmentBulkCompatible {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) : Prop :=
  match instruction with
  | .TableInit _ entry => ∀ element tableId address target segment table,
      code.indirect.val[entry.val]? = some (element, tableId) →
      inst.elems.val[element.val]? = some address → inst.tables.val[tableId.val]? = some target →
      store.elems.val[address.val]? = some segment → store.tables.val[target.index.val]? = some table →
      segment.ty = table.ty
  | _ => True

theorem SegmentBulkCompatible.transport {M : Type} {store after : runtime.store.Store M}
    {inst code instruction} (compatible : SegmentBulkCompatible store inst code instruction)
    (same : SegmentTypes store after) : SegmentBulkCompatible after inst code instruction := by
  cases instruction <;> simp only [SegmentBulkCompatible] at compatible ⊢
  all_goals try trivial
  intro element tableId address target segment table descriptor mapped tableMapped sourceFound targetFound
  have elementTags := congrArg (fun values : List Itasca.types.ElemType => values[address.val]?) same.elements
  have tableTags := congrArg (fun values : List Itasca.types.ElemType => values[target.index.val]?) same.tables
  simp only [List.getElem?_map, sourceFound, Option.map_some] at elementTags
  simp only [List.getElem?_map, targetFound, Option.map_some] at tableTags
  cases oldSource : store.elems.val[address.val]? with
  | none => simp [oldSource] at elementTags
  | some oldSegment =>
    cases oldTarget : store.tables.val[target.index.val]? with
    | none => simp [oldTarget] at tableTags
    | some oldTable =>
      have sourceType : segment.ty = oldSegment.ty := by simpa [oldSource] using elementTags
      have targetType : table.ty = oldTable.ty := by simpa [oldTarget] using tableTags
      rw [sourceType, targetType]
      exact compatible element tableId address target oldSegment oldTable descriptor mapped tableMapped oldSource oldTarget

/-- Source typing and source/raw type-map agreement establish the needed equality
for a compiler-selected active element segment. -/
theorem segment_table_compatible {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (entry element tableId : U32) (segment : Itasca.module.Element) (tableType : Itasca.types.TableType)
    (descriptor : code.indirect.val[entry.val]? = some (element, tableId))
    (source : inst.module.module.env.elements.val[element.val]? = some segment)
    (target : inst.module.module.env.table_types.val[tableId.val]? = some tableType)
    (same : segment.elem = tableType.elem) (bindings : SegmentTypeBindings store inst) :
    SegmentBulkCompatible store inst code (.TableInit 0#u32 entry) := by
  intro actualElement actualTable address tableAddress values table actualDescriptor mapped tableMapped valuesFound tableFound
  have pair := Option.some.inj (actualDescriptor.symm.trans descriptor)
  have first := congrArg Prod.fst pair
  have second := congrArg Prod.snd pair
  dsimp only at first second
  subst actualElement actualTable
  rw [bindings.elements element.val segment address values source mapped valuesFound,
    bindings.tables tableId.val tableType tableAddress table target tableMapped tableFound, same]

end Itasca.Runtime.Store
