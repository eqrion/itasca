import Itasca.Runtime.Store.Initialization.PrecheckWitness
import Itasca.Runtime.Store.Initialization.InitializerSource
import Itasca.Runtime.Store.Invariant.SourceSyntax
import SpecExt.Wasm1
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca

/-- Source segment syntax comes directly from retained canonical metadata. -/
def sourceElements (inst : runtime.store.ModuleInst) : List elem :=
  inst.module.module.env.elements.val.map (ModuleElaboration.element ∘ ModuleEnv.rawElement)

def sourceDatas (inst : runtime.store.ModuleInst) : List data :=
  inst.module.module.tail.data.val.map (ModuleData.translate ∘ ModuleData.raw)

theorem ElementBoundsFailure.source {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (failure : ElementBoundsFailure store inst)
    (storeWf : wf_store (decodeStore view code store))
    (frameWf : wf_frame ⟨[], decodeInstance store inst⟩) :
    SpecExt.Wasm1.SegmentBoundsFailure (decodeStore view code store) (decodeInstance store inst)
      (sourceElements inst) (sourceDatas inst) := by
  obtain ⟨index, segment, target, offset, words, address, table, found, active, resolved,
    mapped, selected, outside⟩ := failure
  apply SpecExt.Wasm1.SegmentBoundsFailure.element
    (index := index.val) (target := target.val)
    (count := ((words[0]?).getD 0#u64).val % 2^32)
    (address := address.index.val) (table := decodeTable table)
    (offset := ModuleConstants.expression offset)
    (referenceType := Translate.referenceType segment.elem)
    (initializers := segment.init.val.map ModuleConstants.expression)
  · simp [sourceElements, List.getElem?_map, found, Function.comp_def,
      ModuleElaboration.element, ModuleEnv.rawElement, active, ModuleSegments.elementMode]
  · exact initializer_resolution_source view code store inst offset .I32 words resolved storeWf frameWf
  · simp [decodeInstance, List.getElem?_map, mapped]
  · simp [decodeStore, List.getElem?_map, selected]
  · simpa [decodeTable] using outside

theorem DataBoundsFailure.source {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (failure : DataBoundsFailure view store inst)
    (storeWf : wf_store (decodeStore view code store))
    (frameWf : wf_frame ⟨[], decodeInstance store inst⟩) :
    SpecExt.Wasm1.SegmentBoundsFailure (decodeStore view code store) (decodeInstance store inst)
      (sourceElements inst) (sourceDatas inst) := by
  obtain ⟨index, segment, target, offset, words, address, memory, found, active, resolved,
    mapped, selected, outside⟩ := failure
  apply SpecExt.Wasm1.SegmentBoundsFailure.data
    (index := index.val) (target := target.val)
    (count := ((words[0]?).getD 0#u64).val % 2^32)
    (address := address.index.val) (memory := decodeMemory view memory)
    (offset := ModuleConstants.expression offset) (bytes := segment.init.val.map (fun b => .mk_byte b.val))
  · simp [sourceDatas, List.getElem?_map, found, Function.comp_def,
      ModuleData.translate, ModuleData.raw, active, ModuleSegments.dataMode]
  · exact initializer_resolution_source view code store inst offset .I32 words resolved storeWf frameWf
  · simp [decodeInstance, List.getElem?_map, mapped]
  · simp [decodeStore, List.getElem?_map, selected]
  · simpa [decodeMemory, decodeBytes] using outside

theorem PrecheckCause.source {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (trap : runtime.Trap)
    (cause : PrecheckCause view store inst (.Trap trap))
    (storeWf : wf_store (decodeStore view code store))
    (frameWf : wf_frame ⟨[], decodeInstance store inst⟩) :
    SpecExt.Wasm1.SegmentBoundsFailure (decodeStore view code store) (decodeInstance store inst)
      (sourceElements inst) (sourceDatas inst) := by
  rcases cause with impossible | ⟨_, element⟩ | ⟨_, data⟩
  · simp [ResourceError] at impossible
  · exact element.source view code store inst storeWf frameWf
  · exact data.source view code store inst storeWf frameWf

/-- The source statement names the independently decoded module's segments. -/
theorem source_segments_raw (inst : runtime.store.ModuleInst) (raw : ModuleBinary.Module)
    (matched : ModuleElaboration.Matches inst.module.module.env inst.module.module.tail raw) :
    sourceElements inst = raw.elements.map ModuleElaboration.element ∧
    sourceDatas inst = raw.data.map ModuleData.translate := by
  have elements := congrArg ModuleBinary.Module.elements matched.1
  have datas := congrArg ModuleBinary.Module.data matched.1
  simp only [ModuleElaboration.fromEnv] at elements datas
  constructor
  · simp [sourceElements, elements, List.map_map, Function.comp_def]
  · simp [sourceDatas, datas, List.map_map, Function.comp_def]
end Itasca.Runtime.Store
