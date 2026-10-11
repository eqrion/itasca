import Itasca.Module.ModuleEnvParser

open Aeneas Aeneas.Std

namespace Itasca.ModuleEnv

open ModuleBinary

/-- Byte chunks assign each custom section to the next declaration slot, or to
    the trailing custom suffix. Future slots are still empty. -/
structure Layout where
  types : List U8 := []
  imports : List U8 := []
  functions : List U8 := []
  tables : List U8 := []
  memories : List U8 := []
  globals : List U8 := []
  exports : List U8 := []
  start : List U8 := []
  elements : List U8 := []
  customs : List U8 := []

def Layout.bytes (l : Layout) : List U8 :=
  l.types ++ l.imports ++ l.functions ++ l.tables ++ l.memories ++ l.globals ++ l.exports ++ l.start ++ l.elements ++ l.customs

def Layout.Future (last : Nat) (l : Layout) : Prop :=
  (last < 1 → l.types = []) ∧
  (last < 2 → l.imports = []) ∧
  (last < 3 → l.functions = []) ∧
  (last < 4 → l.tables = []) ∧
  (last < 5 → l.memories = []) ∧
  (last < 6 → l.globals = []) ∧
  (last < 7 → l.exports = []) ∧
  (last < 8 → l.start = []) ∧
  (last < 9 → l.elements = [])

structure Layout.Valid (last : Nat) (decls : Declarations) (l : Layout)
    (profile : ValidationProfile := .Wasm1) : Prop where
  types : PaddedEncoding 1#u8 (VecEncoding FuncTypeEncoding) [] decls.types l.types
  imports : PaddedEncoding 2#u8 (VecEncoding ImportEncoding) [] decls.imports l.imports
  functions : PaddedEncoding 3#u8 (VecEncoding IndexEncoding) [] decls.functions l.functions
  tables : PaddedEncoding 4#u8 (VecEncoding TableTypeEncoding) [] decls.tables l.tables
  memories : PaddedEncoding 5#u8 (VecEncoding MemTypeEncoding) [] decls.memories l.memories
  globals : PaddedEncoding 6#u8 (VecEncoding GlobalEncoding) [] decls.globals l.globals
  exports : PaddedEncoding 7#u8 (VecEncoding ExportEncoding) [] decls.exports l.exports
  start : PaddedEncoding 8#u8 StartEncoding none decls.start l.start
  elements : PaddedEncoding 9#u8 (VecEncoding (ElementEncodingFor profile)) [] decls.elements l.elements
  customs : CustomsEncoding l.customs
  future : l.Future last

theorem Layout.valid_empty (profile : ValidationProfile := .Wasm1) :
    Layout.Valid 0 ({} : Declarations) ({} : Layout) profile := by
  constructor
  · exact ⟨[], [], .nil, .absent, rfl⟩
  · exact ⟨[], [], .nil, .absent, rfl⟩
  · exact ⟨[], [], .nil, .absent, rfl⟩
  · exact ⟨[], [], .nil, .absent, rfl⟩
  · exact ⟨[], [], .nil, .absent, rfl⟩
  · exact ⟨[], [], .nil, .absent, rfl⟩
  · exact ⟨[], [], .nil, .absent, rfl⟩
  · exact ⟨[], [], .nil, .absent, rfl⟩
  · exact ⟨[], [], .nil, .absent, rfl⟩
  · exact .nil
  · simp [Layout.Future]

theorem Layout.Valid.custom {profile last decls l bytes} (h : Layout.Valid last decls l profile)
    (hc : CustomEncoding bytes) :
    Layout.Valid last decls { l with customs := l.customs ++ bytes } profile := by
  exact ⟨h.types, h.imports, h.functions, h.tables, h.memories, h.globals,
    h.exports, h.start, h.elements,
    by simpa using ModuleTail.customs_append h.customs (.cons hc .nil), h.future⟩

theorem Effect.append_layout {profile} {data origin pos first next env result before after id last l}
    (h : Effect (profile := profile) data first env before id next result after)
    (hh : SectionHeader data pos id first next)
    (hl : Layout.Valid last before l profile) (ho : last < id.val)
    (hs : Wasm.BytesAt data origin l.bytes pos) :
    ∃ updated, Layout.Valid id.val after updated profile ∧ Wasm.BytesAt data origin updated.bytes next := by
  rcases hl.future with ⟨hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9⟩
  cases h with
  | types hadd hb hv =>
    obtain ⟨bytes, he, hbytes⟩ := ModuleTail.header_payload hh hb
    have hz1 : l.types = [] := hf1 (by scalar_tac)
    have hz2 : l.imports = [] := hf2 (by scalar_tac)
    have hz3 : l.functions = [] := hf3 (by scalar_tac)
    have hz4 : l.tables = [] := hf4 (by scalar_tac)
    have hz5 : l.memories = [] := hf5 (by scalar_tac)
    have hz6 : l.globals = [] := hf6 (by scalar_tac)
    have hz7 : l.exports = [] := hf7 (by scalar_tac)
    have hz8 : l.start = [] := hf8 (by scalar_tac)
    have hz9 : l.elements = [] := hf9 (by scalar_tac)
    refine ⟨{ l with types := l.customs ++ bytes, customs := [] }, ?_, ?_⟩
    · constructor
      · exact ⟨l.customs, bytes, hl.customs, .present he, rfl⟩
      · exact hl.imports
      · exact hl.functions
      · exact hl.tables
      · exact hl.memories
      · exact hl.globals
      · exact hl.exports
      · exact hl.start
      · exact hl.elements
      · exact .nil
      · simp [Layout.Future, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hz9]
    · convert hs.append hbytes using 1
      simp [Layout.bytes, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hz9]
  | imports hadd hb =>
    obtain ⟨bytes, he, hbytes⟩ := ModuleTail.header_payload hh hb
    have hz2 : l.imports = [] := hf2 (by scalar_tac)
    have hz3 : l.functions = [] := hf3 (by scalar_tac)
    have hz4 : l.tables = [] := hf4 (by scalar_tac)
    have hz5 : l.memories = [] := hf5 (by scalar_tac)
    have hz6 : l.globals = [] := hf6 (by scalar_tac)
    have hz7 : l.exports = [] := hf7 (by scalar_tac)
    have hz8 : l.start = [] := hf8 (by scalar_tac)
    have hz9 : l.elements = [] := hf9 (by scalar_tac)
    refine ⟨{ l with imports := l.customs ++ bytes, customs := [] }, ?_, ?_⟩
    · constructor
      · exact hl.types
      · exact ⟨l.customs, bytes, hl.customs, .present he, rfl⟩
      · exact hl.functions
      · exact hl.tables
      · exact hl.memories
      · exact hl.globals
      · exact hl.exports
      · exact hl.start
      · exact hl.elements
      · exact .nil
      · simp [Layout.Future, hz3, hz4, hz5, hz6, hz7, hz8, hz9]
    · convert hs.append hbytes using 1
      simp [Layout.bytes, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hz9, List.append_assoc]
  | functions hadd hb =>
    obtain ⟨bytes, he, hbytes⟩ := ModuleTail.header_payload hh hb
    have hz3 : l.functions = [] := hf3 (by scalar_tac)
    have hz4 : l.tables = [] := hf4 (by scalar_tac)
    have hz5 : l.memories = [] := hf5 (by scalar_tac)
    have hz6 : l.globals = [] := hf6 (by scalar_tac)
    have hz7 : l.exports = [] := hf7 (by scalar_tac)
    have hz8 : l.start = [] := hf8 (by scalar_tac)
    have hz9 : l.elements = [] := hf9 (by scalar_tac)
    refine ⟨{ l with functions := l.customs ++ bytes, customs := [] }, ?_, ?_⟩
    · constructor
      · exact hl.types
      · exact hl.imports
      · exact ⟨l.customs, bytes, hl.customs, .present he, rfl⟩
      · exact hl.tables
      · exact hl.memories
      · exact hl.globals
      · exact hl.exports
      · exact hl.start
      · exact hl.elements
      · exact .nil
      · simp [Layout.Future, hz4, hz5, hz6, hz7, hz8, hz9]
    · convert hs.append hbytes using 1
      simp [Layout.bytes, hz3, hz4, hz5, hz6, hz7, hz8, hz9, List.append_assoc]
  | tables hadd hb hv hc =>
    obtain ⟨bytes, he, hbytes⟩ := ModuleTail.header_payload hh hb
    have hz4 : l.tables = [] := hf4 (by scalar_tac)
    have hz5 : l.memories = [] := hf5 (by scalar_tac)
    have hz6 : l.globals = [] := hf6 (by scalar_tac)
    have hz7 : l.exports = [] := hf7 (by scalar_tac)
    have hz8 : l.start = [] := hf8 (by scalar_tac)
    have hz9 : l.elements = [] := hf9 (by scalar_tac)
    refine ⟨{ l with tables := l.customs ++ bytes, customs := [] }, ?_, ?_⟩
    · constructor
      · exact hl.types
      · exact hl.imports
      · exact hl.functions
      · exact ⟨l.customs, bytes, hl.customs, .present he, rfl⟩
      · exact hl.memories
      · exact hl.globals
      · exact hl.exports
      · exact hl.start
      · exact hl.elements
      · exact .nil
      · simp [Layout.Future, hz5, hz6, hz7, hz8, hz9]
    · convert hs.append hbytes using 1
      simp [Layout.bytes, hz4, hz5, hz6, hz7, hz8, hz9, List.append_assoc]
  | memories hadd hb hv hc =>
    obtain ⟨bytes, he, hbytes⟩ := ModuleTail.header_payload hh hb
    have hz5 : l.memories = [] := hf5 (by scalar_tac)
    have hz6 : l.globals = [] := hf6 (by scalar_tac)
    have hz7 : l.exports = [] := hf7 (by scalar_tac)
    have hz8 : l.start = [] := hf8 (by scalar_tac)
    have hz9 : l.elements = [] := hf9 (by scalar_tac)
    refine ⟨{ l with memories := l.customs ++ bytes, customs := [] }, ?_, ?_⟩
    · constructor
      · exact hl.types
      · exact hl.imports
      · exact hl.functions
      · exact hl.tables
      · exact ⟨l.customs, bytes, hl.customs, .present he, rfl⟩
      · exact hl.globals
      · exact hl.exports
      · exact hl.start
      · exact hl.elements
      · exact .nil
      · simp [Layout.Future, hz6, hz7, hz8, hz9]
    · convert hs.append hbytes using 1
      simp [Layout.bytes, hz5, hz6, hz7, hz8, hz9, List.append_assoc]
  | globals hadd hb hv =>
    obtain ⟨bytes, he, hbytes⟩ := ModuleTail.header_payload hh hb
    have hz6 : l.globals = [] := hf6 (by scalar_tac)
    have hz7 : l.exports = [] := hf7 (by scalar_tac)
    have hz8 : l.start = [] := hf8 (by scalar_tac)
    have hz9 : l.elements = [] := hf9 (by scalar_tac)
    refine ⟨{ l with globals := l.customs ++ bytes, customs := [] }, ?_, ?_⟩
    · constructor
      · exact hl.types
      · exact hl.imports
      · exact hl.functions
      · exact hl.tables
      · exact hl.memories
      · exact ⟨l.customs, bytes, hl.customs, .present he, rfl⟩
      · exact hl.exports
      · exact hl.start
      · exact hl.elements
      · exact .nil
      · simp [Layout.Future, hz7, hz8, hz9]
    · convert hs.append hbytes using 1
      simp [Layout.bytes, hz6, hz7, hz8, hz9, List.append_assoc]
  | exports hadd hb =>
    obtain ⟨bytes, he, hbytes⟩ := ModuleTail.header_payload hh hb
    have hz7 : l.exports = [] := hf7 (by scalar_tac)
    have hz8 : l.start = [] := hf8 (by scalar_tac)
    have hz9 : l.elements = [] := hf9 (by scalar_tac)
    refine ⟨{ l with exports := l.customs ++ bytes, customs := [] }, ?_, ?_⟩
    · constructor
      · exact hl.types
      · exact hl.imports
      · exact hl.functions
      · exact hl.tables
      · exact hl.memories
      · exact hl.globals
      · exact ⟨l.customs, bytes, hl.customs, .present he, rfl⟩
      · exact hl.start
      · exact hl.elements
      · exact .nil
      · simp [Layout.Future, hz8, hz9]
    · convert hs.append hbytes using 1
      simp [Layout.bytes, hz7, hz8, hz9, List.append_assoc]
  | start he hb hi =>
    obtain ⟨bytes, he, hbytes⟩ := ModuleTail.header_payload hh hb
    have hz8 : l.start = [] := hf8 (by scalar_tac)
    have hz9 : l.elements = [] := hf9 (by scalar_tac)
    refine ⟨{ l with start := l.customs ++ bytes, customs := [] }, ?_, ?_⟩
    · constructor
      · exact hl.types
      · exact hl.imports
      · exact hl.functions
      · exact hl.tables
      · exact hl.memories
      · exact hl.globals
      · exact hl.exports
      · exact ⟨l.customs, bytes, hl.customs, .present he, rfl⟩
      · exact hl.elements
      · exact .nil
      · simp [Layout.Future, hz9]
    · convert hs.append hbytes using 1
      simp [Layout.bytes, hz8, hz9, List.append_assoc]
  | elements hadd hb hv =>
    obtain ⟨bytes, he, hbytes⟩ := ModuleTail.header_payload hh hb
    have hz9 : l.elements = [] := hf9 (by scalar_tac)
    refine ⟨{ l with elements := l.customs ++ bytes, customs := [] }, ?_, ?_⟩
    · constructor
      · exact hl.types
      · exact hl.imports
      · exact hl.functions
      · exact hl.tables
      · exact hl.memories
      · exact hl.globals
      · exact hl.exports
      · exact hl.start
      · exact ⟨l.customs, bytes, hl.customs, .present he, rfl⟩
      · exact .nil
      · simp [Layout.Future]
    · convert hs.append hbytes using 1
      simp [Layout.bytes, hz9, List.append_assoc]

theorem Run.append_layout {profile} {data initial decls start initialId after afterDecls next id origin l}
    (h : Run (profile := profile) data initial decls start initialId after afterDecls next id)
    (hl : Layout.Valid initialId.val decls l profile)
    (hs : Wasm.BytesAt data origin l.bytes start) :
    ∃ updated, Layout.Valid id.val afterDecls updated profile ∧ Wasm.BytesAt data origin updated.bytes next := by
  induction h with
  | nil => exact ⟨l, hl, hs⟩
  | custom _ hc ih =>
    obtain ⟨current, hv, hb⟩ := ih hl
    obtain ⟨bytes, he, hs⟩ := hc
    exact ⟨{ current with customs := current.customs ++ bytes }, hv.custom he,
      by simpa only [Layout.bytes, List.append_assoc] using hb.append hs⟩
  | step _ ho hh he ih =>
    obtain ⟨current, hv, hb⟩ := ih hl
    exact he.append_layout hh hv ho hb

theorem Layout.Valid.encoding {profile last decls l} (h : Layout.Valid last decls l profile) :
    PrefixEncoding decls (magicVersion ++ l.bytes) profile := by
  exact ⟨l.types, l.imports, l.functions, l.tables, l.memories, l.globals, l.exports,
    l.start, l.elements, l.customs, h.types, h.imports, h.functions, h.tables,
    h.memories, h.globals, h.exports, h.start, h.elements, h.customs,
    by simp only [Layout.bytes, List.append_assoc]⟩

/-- Successful section histories have the full independently encoded prefix. -/
theorem Run.encoding {profile} {data initial start after decls next id}
    (h : Run (profile := profile) data initial {} start 0#u8 after decls next id)
    (hh : Wasm.BytesAt data 0#usize magicVersion start) :
    At (fun decls bytes => PrefixEncoding decls bytes profile) data 0#usize decls next := by
  obtain ⟨layout, hv, hb⟩ := h.append_layout (Layout.valid_empty profile)
    (show Wasm.BytesAt data start (Layout.bytes {}) start from Wasm.BytesAt.nil data start hh.bound)
  exact ⟨magicVersion ++ layout.bytes, hv.encoding, hh.append hb⟩

end Itasca.ModuleEnv
