import Itasca.Module.Readers.FramingComplete
import Itasca.Module.Readers.Names

/-!
# Custom section trace definitions

Definitions for tracing custom section callbacks. An `Event` is a custom section callback,
`RecordsCustom` says a visitor records those events, and `CustomAt` is the independent framing of a
reported custom section. `SectionTrace` walks section intervals and lists the events they emit,
with `EnvTrace` and `TailTrace` as the environment and tail instances.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleTrace

/-- An event observed by a custom section hook. It carries the reported section, with its offsets
in the component byte region. -/
inductive Event where
  | custom (chunk : types.CustomSection)

/-- A successful `on_custom_section` call appends the exact reported section to the observation. -/
def RecordsCustom {V : Type} (visitor : module.ModuleVisitor V) (observe : V → List Event) : Prop :=
  ∀ v chunk v', visitor.on_custom_section v chunk = .ok (.Ok (), v') →
    observe v' = observe v ++ [.custom chunk]

/-- The reported `chunk` is the custom section from `start` to `finish` under independent framing,
including its UTF-8 name and the payload interval that immediately follows the encoded name. -/
def CustomAt (data : Slice U8) (start finish : Usize) (chunk : types.CustomSection) : Prop :=
  ∃ first nm, ModuleBinary.SectionHeader data start 0#u8 first finish ∧
    ModuleBinary.At ModuleBinary.NameEncoding data first nm chunk.payload_start ∧
    chunk.payload_start.val ≤ finish.val ∧ chunk.payload_end = finish ∧ chunk.name_len.val = nm.length

/-- A custom section is nonempty and lies within the data. -/
theorem CustomAt.span {data start finish chunk} (h : CustomAt data start finish chunk) :
    start.val < finish.val ∧ finish.val ≤ data.length := by
  obtain ⟨first, _, hh, _, hp, he, _⟩ := h
  have := hh.span
  omega

/-- The sections from the first position to the second are traversed exactly once, emitting
`events`. Allowed ordinary sections emit no custom callback, and each custom section emits its
independently framed argument. This relation mentions no extracted decoder or callback
execution. -/
inductive SectionTrace (data : Slice U8) (allowed : U8 → Prop) :
    Usize → Usize → List Event → Prop where
  | done (pos : Usize) (hpos : pos.val ≤ data.length) : SectionTrace data allowed pos pos []
  | custom {start middle finish chunk events} : CustomAt data start middle chunk →
      SectionTrace data allowed middle finish events →
      SectionTrace data allowed start finish (.custom chunk :: events)
  | ordinary {start first middle finish id events} : allowed id → id ≠ 0#u8 →
      ModuleBinary.SectionHeader data start id first middle →
      SectionTrace data allowed middle finish events → SectionTrace data allowed start finish events

/-- A section trace advances the position within the data. -/
theorem SectionTrace.span {data allowed start finish events}
    (h : SectionTrace data allowed start finish events) :
    start.val ≤ finish.val ∧ finish.val ≤ data.length := by
  induction h with
  | done => exact ⟨le_rfl, ‹_›⟩
  | custom hc _ ih => have := hc.span; omega
  | ordinary _ _ hh _ ih => have := hh.span; omega

/-- The environment walk starts after the module header and passes through the type to element
sections (ids `1` to `9`) and the data count section (id `12`). -/
def EnvTrace (data : Slice U8) (finish : Usize) (events : List Event) : Prop :=
  ∃ start, Wasm1.BytesAt data 0#usize ModuleBinary.magicVersion start ∧
    SectionTrace data (fun id => (1 ≤ id.val ∧ id.val < 10) ∨ id.val = 12) start finish events

/-- The tail walk from `start` to the end of the input passes through data sections (id `11`). -/
def TailTrace (data : Slice U8) (start : Usize) (events : List Event) : Prop :=
  SectionTrace data (fun id => id = 11#u8) start (Slice.len data) events

end Itasca.ModuleTrace

open Aeneas Aeneas.Std

namespace Itasca.ModuleTrace

/-- The public `name_len` field identifies exactly the UTF-8 bytes immediately before
`payload_start`, as documented by the Rust `CustomSection` API. -/
theorem CustomAt.name_bytes {data start finish chunk} (h : CustomAt data start finish chunk) :
    ∃ nameStart nm, Wasm1.BytesAt data nameStart nm chunk.payload_start ∧ ModuleBinary.Utf8 nm ∧
      nameStart.val + chunk.name_len.val = chunk.payload_start.val ∧ start.val < nameStart.val := by
  obtain ⟨first, nm, hh, hnameAt, hp, he, hlen⟩ := h
  obtain ⟨bytes, hn, hb⟩ := hnameAt
  obtain ⟨count, hc, hbytes⟩ := ModuleBinary.ByteVecEncoding.iff.mp hn.1
  rw [hbytes] at hb
  obtain ⟨nameStart, hcount, hname⟩ := hb.split
  refine ⟨nameStart, nm, hname, hn.2, ?_, ?_⟩
  · have := hname.length
    omega
  · have := hh.span
    have := hcount.length
    omega

/-- Both metadata intervals lie within the original module buffer, so computing the name start by
subtraction cannot underflow. -/
theorem CustomAt.bounds {data start finish chunk} (h : CustomAt data start finish chunk) :
    chunk.name_len.val ≤ chunk.payload_start.val ∧
      chunk.payload_start.val ≤ chunk.payload_end.val ∧ chunk.payload_end.val ≤ data.length := by
  obtain ⟨nameStart, nm, hn, hu, he, hs⟩ := h.name_bytes
  obtain ⟨first, _, hh, _, hp, hend, _⟩ := h
  have := hh.span
  subst finish
  omega

end Itasca.ModuleTrace
