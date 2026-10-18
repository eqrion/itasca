import Exec.Representation.Collection
import Exec.Store.Invariant.InstanceItems
import Exec.Store.Preparation.AllocationShape
import Exec.Store.Invariant.FunctionSignatures

namespace Exec.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

private theorem length_of_prefix {T : Type} {before after : List T}
    (retained : after.take before.length = before) : before.length ≤ after.length := by
  have size := congrArg List.length retained
  simp only [List.length_take] at size
  omega

theorem StagedPrefix.instance_shape {M : Type} {before after : runtime.store.Store M}
    (retained : StagedPrefix before after) (inst : runtime.store.Instance) (shape : InstanceShape before inst) :
    InstanceShape after inst :=
  InstanceShape.mono before after retained.identity.symm
    (length_of_prefix retained.types) (length_of_prefix retained.funcs)
    (length_of_prefix retained.tables) (length_of_prefix retained.memories)
    (length_of_prefix retained.globals) (length_of_prefix retained.elems)
    (length_of_prefix retained.datas) inst shape

theorem StagedPrefix.function_shape {M : Type} {before after : runtime.store.Store M}
    (retained : StagedPrefix before after) (function : runtime.store.Function) (shape : FunctionShape before function) :
    FunctionShape after function := by
  obtain ⟨signature, body⟩ := shape
  refine ⟨Nat.lt_of_lt_of_le signature (length_of_prefix retained.types), ?_⟩
  cases code : function.code with
  | Host id => trivial
  | Wasm instanceIndex functionIndex =>
    simp only [code] at body ⊢
    obtain ⟨inst, found, bound⟩ := body
    exact ⟨inst, Exec.Representation.lookup_prefix _ _ retained.instances found, bound⟩

/-- Retained functions and the concrete newly allocated source-index metadata
supply FunctionShape after the provisional instance has been published. -/
theorem staged_function_shapes {M : Type} {view : M → Slice U8}
    (before after : runtime.store.Store M) (shape : Shape view before)
    (retained : StagedPrefix before after) (inst : runtime.store.Instance)
    (found : after.instances.val[before.instances.len.val]? = some inst)
    {tables memories} (cache : Cache inst.module.module.env tables memories)
    (staged : StagedFunctionSignatures before after before.instances.len
      (inst.module.module.env.func_types.val.drop (importedFuncs inst.module.module.env.imports.val).length)) :
    ∀ function ∈ after.funcs.val, FunctionShape after function := by
  intro function member
  rcases staged function member with old | ⟨index, bound, code, signature⟩
  · exact retained.function_shape function (shape.functions function old)
  · have sizes := cache.funcs.length_eq
    simp only [List.length_append] at sizes
    have definedBound : index.val < inst.module.module.env.func_type_indices.length := by
      simp only [List.length_drop] at bound
      change index.val < inst.module.module.env.func_type_indices.val.length
      omega
    refine ⟨(List.getElem?_eq_some_iff.mp signature).1, ?_⟩
    simp only [code]
    exact ⟨inst, found, definedBound⟩

/-- A source-complete instance is charged exactly the preflight module total. -/
theorem InstanceShape.item_charge {M : Type} {store : runtime.store.Store M}
    (inst : runtime.store.Instance) (shape : InstanceShape store inst) : instanceItems inst = moduleItems inst.module := by
  obtain ⟨types, functions, tables, memories, globals, elements, datas, rest⟩ := shape
  simp only [instanceItems, moduleItems, types, functions, tables, memories, globals, elements, datas]

private theorem append_singleton_of_prefix {T : Type} {before after : List T} {value : T}
    (retained : after.take before.length = before) (size : after.length = before.length + 1)
    (found : after[before.length]? = some value) : after = before ++ [value] := by
  apply List.ext_getElem?
  intro index
  by_cases old : index < before.length
  · have read := congrArg (fun values => values[index]?) retained
    simpa [List.getElem?_take, old, List.getElem?_append] using read
  · by_cases last : index = before.length
    · subst index
      simpa using found
    · have past : after.length ≤ index := by omega
      have pastAppend : (before ++ [value]).length ≤ index := by simp only [List.length_append, List.length_singleton]; omega
      rw [List.getElem?_eq_none past, List.getElem?_eq_none pastAppend]

/-- The final item charge assembles full Store.Shape from the actual allocated
inventory, the completed new instance, and concrete staged function metadata. -/
theorem shape_after_staging {M : Type} (view : M → Slice U8)
    (before after : runtime.store.Store M) (shape : Shape view before)
    (allocated : AllocationShape view after) (retained : StagedPrefix before after)
    (inst : runtime.store.Instance) (found : after.instances.val[before.instances.len.val]? = some inst)
    (instanceShape : InstanceShape after inst)
    (instanceCount : after.instances.length = before.instances.length + 1)
    (instanceRoom : before.instances.length < before.limits.max_instances.val)
    {tables memories} (cache : Cache inst.module.module.env tables memories)
    (staged : StagedFunctionSignatures before after before.instances.len
      (inst.module.module.env.func_types.val.drop (importedFuncs inst.module.module.env.imports.val).length))
    (count : Usize) (counted : count.val = before.instance_items.val + moduleItems inst.module)
    (limited : count.val ≤ after.limits.max_instance_items.val) :
    Shape view {after with instance_items := count} := by
  have instances : after.instances.val = before.instances.val ++ [inst] :=
    append_singleton_of_prefix retained.instances instanceCount found
  have charged := instanceShape.item_charge inst
  have functions := staged_function_shapes before after shape retained inst found cache staged
  constructor
  · exact allocated.identity
  · simpa only [FunctionShape] using functions
  · exact allocated.memories
  · simpa only [TableShape, ReferenceShape] using allocated.tables
  · simpa only [GlobalShape, ReferenceShape] using allocated.globals
  · simpa only [ReferenceShape] using allocated.elements
  · intro entry member
    simp only [instances, List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · exact retained.instance_shape entry (shape.instances entry old)
    · exact instanceShape
  · exact allocated.canonicalTypes
  · have bound := allocated.objectLimit
    unfold objectCount at bound
    dsimp only
    omega
  · dsimp only
    rw [retained.limits, instanceCount]
    omega
  · dsimp only
    simp [instances, counted, shape.instanceAccounting, charged]
  · exact limited
  · exact allocated.signatureAccounting
  · exact allocated.signatureLimit
  · exact allocated.memoryAccounting
  · exact allocated.memoryLimit
  · exact allocated.tableAccounting
  · exact allocated.tableLimit

end Exec.Store
