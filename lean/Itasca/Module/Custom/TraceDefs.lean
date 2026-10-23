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

/-- The environment walk starts after the module header and passes through the type to element
sections (ids `1` to `9`) and the data count section (id `12`). -/
def EnvTrace (data : Slice U8) (finish : Usize) (events : List Event) : Prop :=
  ∃ start, Wasm1.BytesAt data 0#usize ModuleBinary.magicVersion start ∧
    SectionTrace data (fun id => (1 ≤ id.val ∧ id.val < 10) ∨ id.val = 12) start finish events

end Itasca.ModuleTrace

open Aeneas Aeneas.Std

namespace Itasca.ModuleTrace

end Itasca.ModuleTrace
