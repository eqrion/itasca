import Itasca.Module.Env.ReadyContexts
import Itasca.Module.Sections.Tail
import Itasca.Module.Env.NameFacts

/-!
# Materializing independent data segments

Turns independently encoded data segments into runtime `metadata.Data` values without running the
parser. The counts in the binary grammar bound every vector length (`.length_bounded`), so
`DataEncodingFor.materialize` and `ModuleTail.Encoding.materialize` produce the segments, and
`ModuleTail.materialize` also shows they are `ModuleData.Valid` in the ready environment. The
tail completeness proof in `Module/Sections/TailComplete` uses these.
-/

open Aeneas Aeneas.Std alloc.vec

namespace Itasca.ModuleBinary

/-- A vector encoding has at most `Usize.max` elements, because its count is a `u32`. -/
theorem VecEncoding.length_bounded {α : Type} {R : α → List U8 → Prop}
    {values bytes} (h : VecEncoding R values bytes) : values.length ≤ Usize.max := by
  obtain ⟨_, _, hc, _, _⟩ := h
  have hn := hc.value_lt
  scalar_tac

/-- A padded vector section has at most `Usize.max` elements. -/
theorem PaddedEncoding.length_bounded {α : Type} {R : α → List U8 → Prop}
    {id values bytes} (h : PaddedEncoding id (VecEncoding R) [] values bytes) :
    values.length ≤ Usize.max := by
  obtain ⟨_, _, _, hs, _⟩ := h
  cases hs with
  | absent => simp
  | present hp =>
    obtain ⟨_, _, _, hv, _⟩ := hp
    exact hv.length_bounded

/-- A data segment's bytes fit in `Usize`. -/
theorem DataEncoding.init_bounded {entry bytes} (h : DataEncoding entry bytes) :
    entry.init.length ≤ Usize.max := by
  obtain ⟨_, _, _, _, _, _, _, _, hi, _⟩ := h
  exact VecEncoding.length_bounded hi

/-- A profile data segment's bytes fit in `Usize`. -/
theorem DataEncodingFor.init_bounded {profile entry bytes}
    (h : DataEncodingFor profile entry bytes) : entry.init.length ≤ Usize.max := by
  cases profile with
  | Wasm1 => exact DataEncoding.init_bounded h
  | Wasm2 =>
    cases h with
    | active _ _ hi => exact hi.length_bounded
    | passive _ hi => exact hi.length_bounded

/-- A `DataEncodingFor` entry is the raw form of some runtime `metadata.Data`. -/
theorem DataEncodingFor.materialize {profile entry bytes}
    (h : DataEncodingFor profile entry bytes) :
    ∃ segment : metadata.Data, ModuleData.raw segment = entry := by
  refine ⟨⟨entry.mode, Vec.from entry.init h.init_bounded⟩, ?_⟩
  simp [ModuleData.raw]

end Itasca.ModuleBinary

namespace Itasca.ModuleTail

open ModuleBinary

private theorem materialize_list {profile} (entries : List ModuleBinary.Data)
    (h : ∀ entry ∈ entries, ∃ bytes, DataEncodingFor profile entry bytes) :
    ∃ segments : List metadata.Data, segments.map ModuleData.raw = entries := by
  induction entries with
  | nil => exact ⟨[], rfl⟩
  | cons entry entries ih =>
    obtain ⟨_, he⟩ := h entry (by simp)
    obtain ⟨segment, hs⟩ := he.materialize
    obtain ⟨segments, hss⟩ := ih (fun e hm => h e (by simp [hm]))
    exact ⟨segment :: segments, by simp [hs, hss]⟩

/-- A tail encoding's segments are the raw form of some runtime vector of `metadata.Data`. The
allocation bounds come from the data count and each segment's byte count, and no parser
acceptance is assumed. -/
theorem Encoding.materialize {profile entries bytes} (h : Encoding entries bytes profile) :
    ∃ segments : Vec metadata.Data, segments.val.map ModuleData.raw = entries := by
  obtain ⟨_, _, hp, _, _⟩ := h
  obtain ⟨segments, hs⟩ := materialize_list entries (fun entry hm => hp.member hm)
  have hn : segments.length ≤ Usize.max := by
    have := hp.length_bounded
    simpa [← hs] using this
  exact ⟨Vec.from segments hn, by simpa using hs⟩

end Itasca.ModuleTail

namespace Itasca.ModuleEnv

open ModuleElaboration

/-- Segments matching typed raw data are `ModuleData.Valid` in a ready environment. -/
theorem Ready.data_valid {raw decls env} (hready : Ready raw 10 decls env)
    (htyped : SectionsTyped raw) {segments : Vec metadata.Data}
    (hmap : segments.val.map ModuleData.raw = raw.data) :
    ∀ segment ∈ segments.val, ModuleData.Valid env segment := by
  intro segment hm
  have hr : ModuleData.raw segment ∈ raw.data := by
    rw [← hmap]
    exact List.mem_map.mpr ⟨segment, hm, rfl⟩
  apply data_valid_of_typing (hready.initializer_globals (by decide))
  · simpa [ModuleConstants.FunctionContext, initializerContextOf] using hready.funcs_context (by decide)
  · simpa [initializerContextOf] using hready.memories_context (by decide)
  · exact htyped.data _ hr

end Itasca.ModuleEnv

namespace Itasca.ModuleTail

/-- An independently encoded tail whose sections are typed gives runtime segments that match the
raw data and are valid in the ready environment. -/
theorem materialize {profile} (data : Slice U8) (start next : Usize)
    (raw : ModuleBinary.Module) (decls : ModuleEnv.Declarations) (env : metadata.Env)
    (hb : ModuleBinary.At (fun es bs => Encoding es bs profile) data start raw.data next)
    (htyped : ModuleElaboration.SectionsTyped raw)
    (hready : ModuleEnv.Ready raw 10 decls env) :
    ∃ segments : Vec metadata.Data, segments.val.map ModuleData.raw = raw.data ∧
      ∀ segment ∈ segments.val, ModuleData.Valid env segment := by
  obtain ⟨_, he, _⟩ := hb
  obtain ⟨segments, hs⟩ := he.materialize
  exact ⟨segments, hs, hready.data_valid htyped hs⟩

end Itasca.ModuleTail
