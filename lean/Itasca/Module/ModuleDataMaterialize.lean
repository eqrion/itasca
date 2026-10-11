import Itasca.Module.ModuleReadyContexts
import Itasca.Module.ModuleTail
import Itasca.Module.ModuleNameFacts

open Aeneas Aeneas.Std alloc.vec

namespace Itasca.ModuleBinary

/-- The binary vector count itself supplies the runtime allocation bound. -/
theorem VecEncoding.length_bounded {α : Type} {R : α → List U8 → Prop}
    {values bytes} (h : VecEncoding R values bytes) : values.length ≤ Usize.max := by
  obtain ⟨_, _, hc, _, _⟩ := h
  have hn := hc.value_lt
  scalar_tac

theorem PaddedEncoding.length_bounded {α : Type} {R : α → List U8 → Prop}
    {id values bytes} (h : PaddedEncoding id (VecEncoding R) [] values bytes) :
    values.length ≤ Usize.max := by
  obtain ⟨_, _, _, hs, _⟩ := h
  cases hs with
  | absent => simp
  | present hp =>
    obtain ⟨_, _, _, hv, _⟩ := hp
    exact hv.length_bounded

theorem DataEncoding.init_bounded {entry bytes} (h : DataEncoding entry bytes) :
    entry.init.length ≤ Usize.max := by
  obtain ⟨_, _, _, _, _, _, _, _, hi, _⟩ := h
  exact VecEncoding.length_bounded hi

/-- Reify the independently encoded data record without running the parser. -/
theorem DataEncoding.materialize {entry bytes} (h : DataEncoding entry bytes) :
    ∃ segment : module.Data, ModuleData.raw segment = entry := by
  refine ⟨⟨entry.mode, Vec.from entry.init h.init_bounded⟩, ?_⟩
  simp [ModuleData.raw]


theorem DataEncodingFor.init_bounded {profile entry bytes}
    (h : DataEncodingFor profile entry bytes) : entry.init.length ≤ Usize.max := by
  cases profile with
  | Wasm1 => exact DataEncoding.init_bounded h
  | Wasm2 =>
    cases h with
    | active _ _ hi => exact hi.length_bounded
    | passive _ hi => exact hi.length_bounded

theorem DataEncodingFor.materialize {profile entry bytes}
    (h : DataEncodingFor profile entry bytes) :
    ∃ segment : module.Data, ModuleData.raw segment = entry := by
  refine ⟨⟨entry.mode, Vec.from entry.init h.init_bounded⟩, ?_⟩
  simp [ModuleData.raw]

end Itasca.ModuleBinary

namespace Itasca.ModuleTail

open ModuleBinary

private theorem materialize_list {profile} (entries : List ModuleBinary.Data)
    (h : ∀ entry ∈ entries, ∃ bytes, DataEncodingFor profile entry bytes) :
    ∃ segments : List module.Data, segments.map ModuleData.raw = entries := by
  induction entries with
  | nil => exact ⟨[], rfl⟩
  | cons entry entries ih =>
    obtain ⟨_, he⟩ := h entry (by simp)
    obtain ⟨segment, hs⟩ := he.materialize
    obtain ⟨segments, hss⟩ := ih (fun e hm => h e (by simp [hm]))
    exact ⟨segment :: segments, by simp [hs, hss]⟩

/-- Both allocation bounds come from the binary grammar: the data count and
each segment's byte-vector count. No parser acceptance is assumed. -/
theorem Encoding.materialize {profile entries bytes} (h : Encoding entries bytes profile) :
    ∃ segments : Vec module.Data, segments.val.map ModuleData.raw = entries := by
  obtain ⟨_, _, hp, _, _⟩ := h
  obtain ⟨segments, hs⟩ := materialize_list entries (fun entry hm => hp.member hm)
  have hn : segments.length ≤ Usize.max := by
    have := hp.length_bounded
    simpa [← hs] using this
  exact ⟨Vec.from segments hn, by simpa using hs⟩

end Itasca.ModuleTail

namespace Itasca.ModuleEnv

open ModuleElaboration

theorem Ready.data_valid {raw decls env} (hready : Ready raw 10 decls env)
    (htyped : SectionsTyped raw) {segments : Vec module.Data}
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

/-- The independent tail bytes and generated section typing determine runtime
segments suitable for the actual tail-completeness theorem. -/
theorem materialize {profile} (data : Slice U8) (start next : Usize)
    (raw : ModuleBinary.Module) (decls : ModuleEnv.Declarations) (env : module.Env)
    (hb : ModuleBinary.At (fun es bs => Encoding es bs profile) data start raw.data next)
    (htyped : ModuleElaboration.SectionsTyped raw)
    (hready : ModuleEnv.Ready raw 10 decls env) :
    ∃ segments : Vec module.Data, segments.val.map ModuleData.raw = raw.data ∧
      ∀ segment ∈ segments.val, ModuleData.Valid env segment := by
  obtain ⟨_, he, _⟩ := hb
  obtain ⟨segments, hs⟩ := he.materialize
  exact ⟨segments, hs, hready.data_valid htyped hs⟩

end Itasca.ModuleTail
