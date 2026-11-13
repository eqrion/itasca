import Itasca.Runtime.Compiler.Module.SegmentSource
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ModuleBinary

private theorem vector_length_bound {α : Type} {R : α → List U8 → Prop} {values bytes}
    (encoded : VecEncoding R values bytes) : values.length < 2^32 := by
  obtain ⟨count, entries, bounded, _, _⟩ := encoded
  exact bounded.value_lt

private theorem element_payload_bound {entry bytes}
    (encoded : ElementEncodingFor entry bytes) : entry.init.length < 2^32 := by
  cases encoded with
  | activeIndices _ _ encoded | passiveIndices _ encoded | explicitIndices _ _ _ encoded
  | declarativeIndices _ encoded | activeExpressions _ _ encoded | passiveExpressions _ encoded
  | explicitExpressions _ _ _ encoded | declarativeExpressions _ encoded =>
    simpa using vector_length_bound encoded

private theorem data_payload_bound {entry bytes}
    (encoded : DataEncodingFor entry bytes) : entry.init.length < 2^32 := by
  cases encoded with
  | active _ _ encoded | passive _ encoded => exact vector_length_bound encoded

private theorem rep_property {α : Type} {R : α → List U8 → Prop} {Q : α → Prop} {values bytes}
    (encoded : Rep R values bytes) (property : ∀ value bytes, R value bytes → Q value) :
    ∀ value ∈ values, Q value := by
  induction encoded with
  | nil => simp
  | cons head tail ih =>
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact property _ _ head
    · exact ih value member

private theorem padded_property {α : Type} {R : α → List U8 → Prop} {Q : α → Prop} {id values bytes}
    (encoded : PaddedEncoding id (VecEncoding R) [] values bytes)
    (property : ∀ value bytes, R value bytes → Q value) : ∀ value ∈ values, Q value := by
  obtain ⟨customs, sec, _, secProof, _⟩ := encoded
  cases secProof with
  | absent => simp
  | present content =>
    obtain ⟨size, payload, _, ⟨count, entries, _, encoded, _⟩, _⟩ := content
    exact rep_property encoded property

/-- Binary vector prefixes bound every element and data payload, independently
of semantic typing and of the compiler's chosen instruction representation. -/
theorem module_segment_payload_bounds {R raw bytes}
    (encoded : ModuleEncodingWith R raw bytes) :
    (∀ element ∈ raw.elements, element.init.length < 2^32) ∧
    (∀ segment ∈ raw.data, segment.init.length < 2^32) := by
  obtain ⟨types, imports, functions, tables, memories, globals, exports, start, elements, dataCount,
    codes, datas, customs, _, _, _, _, _, _, _, _, hel, _, _, hd, _, _, _⟩ := encoded
  exact ⟨padded_property hel (fun _ _ h => element_payload_bound h),
    padded_property hd (fun _ _ h => data_payload_bound h)⟩

/-- Payload bounds for the actual metadata retained by an accepted validator. -/
theorem validated_segment_payload_bounds {bytes module}
    (validated : Itasca.ModuleSound.Validated bytes module) :
    (∀ element ∈ module.env.elements.val, element.init.length < 2^32) ∧
    (∀ segment ∈ module.tail.data.val, segment.init.length < 2^32) := by
  obtain ⟨raw, encoded, _, matched, _⟩ := validated
  obtain ⟨elements, datas⟩ := module_segment_payload_bounds encoded
  have he := congrArg Itasca.ModuleBinary.Module.elements matched.1
  have hd := congrArg Itasca.ModuleBinary.Module.data matched.1
  constructor
  · intro element member
    apply elements (Itasca.ModuleEnv.rawElement element)
    rw [he]
    exact List.mem_map.mpr ⟨element, member, rfl⟩
  · intro segment member
    apply datas (Itasca.ModuleData.raw segment)
    rw [hd]
    exact List.mem_map.mpr ⟨segment, member, rfl⟩

/-- The public compiler supplies the payload bounds without an added count premise. -/
theorem compile_segment_payload_bounds {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (bytes : Slice U8)
    (limits : runtime.compiler.CompileLimits) (module : runtime.compiler.ExecutableModule)
    (accepted : runtime.compiler.compile_with allocator bytes limits = .ok (.Ok module)) :
    (∀ element ∈ module.module.env.elements.val, element.init.length < 2^32) ∧
    (∀ segment ∈ module.module.tail.data.val, segment.init.length < 2^32) := by
  exact validated_segment_payload_bounds (compile_source_validated allocator law bytes limits module accepted).1
end Itasca.Runtime.Compiler
