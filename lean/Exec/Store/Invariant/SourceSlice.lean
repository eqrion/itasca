import Exec.Code.Local.Source.SourceFunctionTyping
import Exec.Store.Invariant.CodeAgreement
import Exec.Store.Invariant.FunctionSignatures
import Exec.Store.Initialization.SegmentCodeMetadata
import Exec.Interp.Invocation.SliceReadback
namespace Exec.Store
open Aeneas Aeneas.Std Itasca.ModuleEnv

/-- The installed source subset is preserved for old functions and established
for every new defined function by its actual source index. -/
theorem store_slice_publish {M : Type} (view : M → Slice U8)
    (before after : runtime.store.Store M) (oldCode : CodeInterpretation)
    (shape : Shape view before) (retained : StagedPrefix before after)
    (oldSlice : Abs.StoreSlice (decodeStore view oldCode before))
    (inst : runtime.store.Instance) (sources : List funccode)
    (sourceCount : sources.length = inst.module.module.env.func_type_indices.val.length)
    (supported : ∀ source ∈ sources, match source with
      | .HOST _ => False | .FUNC _ _ body => Forall Abs.SliceInstr body)
    (found : after.instances.val[before.instances.len.val]? = some inst)
    {tables memories} (cache : Cache inst.module.module.env tables memories)
    (staged : StagedFunctionSignatures before after before.instances.len
      (inst.module.module.env.func_types.val.drop (importedFuncs inst.module.module.env.imports.val).length)) :
    Abs.StoreSlice (decodeStore view (installCode oldCode before.instances.len.val sources) after) := by
  intro decoded present
  obtain ⟨function, member, rfl⟩ := List.mem_map.mp present
  rcases staged function member with old | ⟨index, bound, encoded, signature⟩
  · rw [decodeFunction_prefix _ before after retained view shape function old]
    simp only [alloc.vec.Vec.len_val]
    rw [decodeFunction_code_agrees (installCode_agrees before oldCode sources) function]
    exact oldSlice _ (List.mem_map.mpr ⟨function, old, rfl⟩)
  · have resolves := List.forall₂_drop (importedFuncs inst.module.module.env.imports.val).length cache.funcs
    have count : inst.module.module.env.func_type_indices.val.length =
        (inst.module.module.env.func_types.val.drop (importedFuncs inst.module.module.env.imports.val).length).length := by
      simpa only [List.drop_left] using resolves.length_eq
    have sourceBound : index.val < sources.length := by rw [sourceCount, count]; exact bound
    let source := sources[index.val]
    have sourceFound : sources[index.val]? = some source := List.getElem?_eq_getElem sourceBound
    have known := supported source (List.mem_of_getElem? sourceFound)
    simp only [decodeFunction, encoded, found,
      installCode_lookup oldCode before.instances.len.val sources inst.module index.val source sourceFound]
    cases same : source <;> simpa only [same] using known

/-- Segment initialization changes no source bodies, even when it traps. -/
theorem SegmentAddressSpace.slice {M : Type} {before after : runtime.store.Store M}
    (metadata : SegmentAddressSpace before after) (view : M → Slice U8) (code : CodeInterpretation)
    (supported : Abs.StoreSlice (decodeStore view code before)) :
    Abs.StoreSlice (decodeStore view code after) := by
  have same : decodeFunction code after = decodeFunction code before := by
    funext function
    simp only [decodeFunction, decodeInstance, metadata.signatures, metadata.instances]
  simpa only [Abs.StoreSlice, decodeStore, metadata.functions, same] using supported

end Exec.Store
